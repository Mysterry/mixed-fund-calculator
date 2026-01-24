#!/usr/bin/env python3
"""Capital Gain Calculator main module."""

from __future__ import annotations

from collections import defaultdict
import datetime
import decimal
from decimal import Decimal
import logging
import sys
from typing import TYPE_CHECKING

from cgt_calc.parsers.remittance import OWREvent, TaxFilings, TaxFilingBasis, Destination, Origin
from . import render_latex
from .args_parser import create_parser
from .const import (
    BED_AND_BREAKFAST_DAYS,
    CAPITAL_GAIN_ALLOWANCES,
    DIVIDEND_ALLOWANCES,
    DIVIDEND_DOUBLE_TAXATION_RULES,
    ERI_TAX_DATE_DELTA,
    INTERNAL_START_DATE,
    UK_CURRENCY,
)
from .currency_converter import CurrencyConverter
from .current_price_fetcher import CurrentPriceFetcher
from .dates import get_tax_year_end, get_tax_year_start, is_date, get_tax_year_index_from_date
from .exceptions import (
    AmountMissingError,
    CalculatedAmountDiscrepancyError,
    CalculationError,
    CgtError,
    InvalidTransactionError,
    PriceMissingError,
    QuantityMissingError,
    QuantityNotPositiveError,
    SymbolMissingError,
)
from .initial_prices import InitialPrices
from .isin_converter import IsinConverter
from .model import (
    ActionType,
    BrokerTransaction,
    CalculationEntry,
    CalculationLog,
    CalculationType,
    CapitalGainsReport,
    Dividend,
    ExcessReportedIncome,
    ExcessReportedIncomeDistribution,
    ExcessReportedIncomeDistributionLog,
    ExcessReportedIncomeLog,
    ForeignAmountLog,
    ForeignCurrencyAmount,
    HmrcTransactionData,
    HmrcTransactionLog,
    PortfolioEntry,
    Position,
    RuleType,
    SpinOff,
    MixedFund,
    ProcessedMixedFundTransaction,
    MixedFundsReport,
    MixedFundMoneyCategory,
    aggregate_dicts, MixedFundEntry, RemittedIncomeType
)
from .parsers import read_broker_transactions
from .parsers.remittance import read_remittance_basis, read_owr
from .setup_logging import setup_logging
from .spin_off_handler import SpinOffHandler
from .transaction_log import add_to_list, has_key
from .util import approx_equal, round_decimal

if TYPE_CHECKING:
    import argparse

LOGGER = logging.getLogger(__name__)


def get_amount_or_fail(transaction: BrokerTransaction) -> Decimal:
    """Return the transaction amount or throw an error."""
    amount = transaction.amount
    if amount is None:
        raise AmountMissingError(transaction)
    return amount


def get_symbol_or_fail(transaction: BrokerTransaction) -> str:
    """Return the transaction symbol or throw an error."""
    symbol = transaction.symbol
    if symbol is None:
        raise SymbolMissingError(transaction)
    return symbol


def get_quantity_or_fail(transaction: BrokerTransaction) -> Decimal:
    """Return the transaction quantity or throw an error."""
    quantity = transaction.quantity
    if quantity is None:
        raise QuantityMissingError(transaction)
    return quantity


# Amount difference can be caused by rounding errors in the price.
# Schwab rounds down the price to 4 decimal places
#  so that the error in amount can be more than $0.01.
# Fox example:
# 500 shares of FOO sold at $100.00016 with $1.23 fees.
# "01/01/2024,"Sell","FOO","FOO","500","$100.0001","$1.23","$49,998.85"
# calculated_amount = 500 * 100.0001 - 1.23 = 49998.82
# amount_on_record = 49998.85 vs calculated_amount = 49998.82
def _approx_equal_price_rounding(
    amount_on_record: Decimal,
    quantity_on_record: Decimal,
    price_on_record: Decimal,
    fees_on_record: Decimal,
    calculation_type: CalculationType,
) -> bool:
    calculated_amount = Decimal(0)
    calculated_price = Decimal(0)
    if calculation_type is CalculationType.ACQUISITION:
        calculated_amount = Decimal(-1) * (
            quantity_on_record * price_on_record + fees_on_record
        )
        calculated_price = (
            Decimal(-1) * amount_on_record - fees_on_record
        ) / quantity_on_record
    elif calculation_type is CalculationType.DISPOSAL:
        calculated_amount = quantity_on_record * price_on_record - fees_on_record
        calculated_price = (amount_on_record + fees_on_record) / quantity_on_record
    in_acceptable_range = abs(calculated_price - price_on_record) < Decimal("0.0001")
    LOGGER.debug(
        "Price calculated_price %.6f vs price_on_record %s in %s",
        calculated_price,
        price_on_record,
        "acceptable range" if in_acceptable_range else "error",
    )
    if in_acceptable_range:
        return True
    accptable_amount = approx_equal(amount_on_record, calculated_amount)
    LOGGER.debug(
        "Amount amount_on_record %.6f vs calculated_amount %s in %s",
        amount_on_record,
        calculated_amount,
        "acceptable range" if accptable_amount else "error",
    )
    return accptable_amount


class CapitalGainsCalculator:
    """Main calculator class."""

    def __init__(
        self,
        tax_year: int,
        currency_converter: CurrencyConverter,
        isin_converter: IsinConverter,
        price_fetcher: CurrentPriceFetcher,
        spin_off_handler: SpinOffHandler,
        initial_prices: InitialPrices,
        interest_fund_tickers: list[str],
        tax_filings: TaxFilings,
        owr_events: list[OWREvent],
        balance_check: bool = True,
        calc_unrealized_gains: bool = False,
    ):
        """Create calculator object."""
        self.tax_year = tax_year

        self.tax_year_start_date = get_tax_year_start(tax_year)
        self.tax_year_end_date = get_tax_year_end(tax_year)

        self.currency_converter = currency_converter
        self.isin_converter = isin_converter
        self.price_fetcher = price_fetcher
        self.spin_off_handler = spin_off_handler
        self.initial_prices = initial_prices
        self.balance_check = balance_check
        self.calc_unrealized_gains = calc_unrealized_gains
        self.interest_fund_tickers = interest_fund_tickers
        self.tax_filings = tax_filings
        self.owr_events = owr_events
        self.total_uk_interest = Decimal(0)
        self.total_foreign_interest = Decimal(0)

        self.acquisition_list: HmrcTransactionLog = {}
        self.disposal_list: HmrcTransactionLog = {}
        self.bnb_list: HmrcTransactionLog = {}
        self.split_list: dict[tuple[str, datetime.date], Decimal] = {}

        self.dividend_list: ForeignAmountLog = defaultdict(ForeignCurrencyAmount)
        self.dividend_tax_list: ForeignAmountLog = defaultdict(ForeignCurrencyAmount)
        self.interest_list: dict[
            tuple[str, str, datetime.date], ForeignCurrencyAmount
        ] = defaultdict(ForeignCurrencyAmount)

        # Log for the report section related only to interests and dividends
        self.calculation_log_yields: CalculationLog = defaultdict(dict)

        self.portfolio: dict[str, Position] = defaultdict(Position)
        self.spin_offs: dict[datetime.date, list[SpinOff]] = defaultdict(list)
        self.eris: ExcessReportedIncomeLog = defaultdict(dict)
        self.eris_distribution: ExcessReportedIncomeDistributionLog = defaultdict(
            lambda: defaultdict(ExcessReportedIncomeDistribution)
        )

        self.mixed_funds: dict[str, MixedFund] = {}

    def date_in_tax_year(self, date: datetime.date) -> bool:
        """Check if date is within current tax year."""
        assert is_date(date)
        return self.tax_year_start_date <= date <= self.tax_year_end_date

    def get_eri(self, symbol: str, date: datetime.date) -> ExcessReportedIncome | None:
        """Return Excess Reported Income at specific date for the input symbol."""
        if date in self.eris and symbol in self.eris[date]:
            return self.eris[date][symbol]
        return None

    def add_acquisition(
        self,
        transaction: BrokerTransaction,
    ) -> None:
        """Add new acquisition to the given list."""
        symbol = get_symbol_or_fail(transaction)
        quantity = transaction.quantity
        price = transaction.price

        if quantity is None or quantity <= 0:
            raise QuantityNotPositiveError(transaction)

        # Add to acquisition_list to apply same day rule
        if transaction.action is ActionType.STOCK_ACTIVITY:
            if price is None:
                price = self.initial_prices.get(transaction.date, symbol)
            amount = round_decimal(quantity * price, 2)
        elif transaction.action is ActionType.SPIN_OFF:
            price, amount = self.handle_spin_off(transaction)
        elif transaction.action is ActionType.STOCK_SPLIT:
            price = Decimal(0)
            amount = Decimal(0)
        else:
            if price is None:
                raise PriceMissingError(transaction)

            amount = get_amount_or_fail(transaction)
            calculated_amount = quantity * price + transaction.fees
            if not _approx_equal_price_rounding(
                amount,
                quantity,
                price,
                transaction.fees,
                CalculationType.ACQUISITION,
            ):
                raise CalculatedAmountDiscrepancyError(transaction, -calculated_amount)
            amount = -amount

        self.portfolio[symbol] += Position(quantity, amount)

        add_to_list(
            self.acquisition_list,
            transaction.date,
            symbol,
            quantity,
            self.currency_converter.to_gbp_for(amount, transaction, LOGGER),
            self.currency_converter.to_gbp_for(transaction.fees, transaction, LOGGER),
        )


    def handle_spin_off(
        self,
        transaction: BrokerTransaction,
    ) -> tuple[Decimal, Decimal]:
        """Handle spin off transaction.

        Doc basing on SOLV spin off out of MMM.

        # 1. Determine the Cost Basis (Acquisition Cost) of the SOLV Shares
        In the UK, the cost basis (or acquisition cost) of the new SOLV shares
        received from the spin-off needs to be determined. This is usually done
        by apportioning part of the original cost basis of the MMM shares to
        the new SOLV shares based on their market values at the time of the
        spin-off.

        ## Step-by-Step Allocation
        * Find the Market Values:

        Determine the market value of MMM shares and SOLV shares immediately
        after the spin-off.

        * Calculate the Apportionment:

        Divide the market value of the MMM shares by the total market value of
        both MMM and SOLV shares to find the percentage allocated to MMM.
        Do the same for SOLV shares to find the percentage allocated to SOLV.

        * Allocate the Original Cost Basis:

        Multiply the original cost basis of your MMM shares by the respective
        percentages to allocate the cost basis between the MMM and SOLV shares.

        ## Example Allocation
        * Original Investment:

        Assume you bought 100 shares of MMM at £100 per share, so your total
        cost basis is £10,000.

        * Market Values Post Spin-off:

        Assume the market value of MMM shares is £90 per share and SOLV shares
        is £10 per share immediately after the spin-off.
        The total market value is £90 + £10 = £100.

        * Allocation Percentages:

        Percentage allocated to MMM: 90/100 = 90%
        Percentage allocated to SOLV: 10/100 = 10%

        * Allocate Cost Basis:

        Cost basis of MMM: £10,000 * 0.90 = £9,000
        Cost basis of SOLV: £10,000 * 0.10 = £1,000

        # 2. Determine the Holding Period
        The holding period for the SOLV shares typically includes the holding
        period of the original MMM shares. This means the date you acquired the
        MMM shares will be used as the acquisition date for the SOLV shares.
        """
        symbol = get_symbol_or_fail(transaction)
        quantity = transaction.quantity
        assert quantity is not None

        ticker = self.spin_off_handler.get_spin_off_source(
            symbol, transaction.date, self.portfolio
        )
        dst_price = self.price_fetcher.get_closing_price(symbol, transaction.date)
        src_price = self.price_fetcher.get_closing_price(ticker, transaction.date)
        dst_amount = quantity * dst_price
        src_amount = self.portfolio[ticker].quantity * src_price
        original_src_amount = self.portfolio[ticker].amount

        share_of_original_cost = src_amount / (dst_amount + src_amount)
        self.spin_offs[transaction.date].append(
            SpinOff(
                dest=symbol,
                source=ticker,
                cost_proportion=share_of_original_cost,
                date=transaction.date,
            )
        )

        amount = (1 - share_of_original_cost) * original_src_amount
        return amount / quantity, round_decimal(amount, 2)

    def add_disposal(
        self,
        transaction: BrokerTransaction,
    ) -> None:
        """Add new disposal to the given list."""
        symbol = get_symbol_or_fail(transaction)
        quantity = transaction.quantity
        if symbol not in self.portfolio:
            raise InvalidTransactionError(
                transaction, "Tried to sell not owned symbol, reversed order?"
            )
        if quantity is None or quantity <= 0:
            raise QuantityNotPositiveError(transaction)
        if self.portfolio[symbol].quantity < quantity:
            raise InvalidTransactionError(
                transaction,
                "Tried to sell more than the available "
                f"balance({self.portfolio[symbol].quantity})",
            )

        amount = get_amount_or_fail(transaction)
        price = transaction.price

        self.portfolio[symbol] -= Position(quantity, amount)

        if self.portfolio[symbol].quantity == 0:
            del self.portfolio[symbol]

        if price is None:
            raise PriceMissingError(transaction)
        calculated_amount = quantity * price - transaction.fees
        if not _approx_equal_price_rounding(
            amount,
            quantity,
            price,
            transaction.fees,
            CalculationType.DISPOSAL,
        ):
            raise CalculatedAmountDiscrepancyError(transaction, calculated_amount)
        add_to_list(
            self.disposal_list,
            transaction.date,
            symbol,
            quantity,
            self.currency_converter.to_gbp_for(amount, transaction, LOGGER),
            self.currency_converter.to_gbp_for(transaction.fees, transaction, LOGGER),
        )

    def add_eri(
        self,
        transaction: BrokerTransaction,
    ) -> None:
        """Add an Excess Reported Income to the list.

        UK has a specific tax regime which applies to UK investors in offshore
        funds.

        https://www.gov.uk/government/publications/offshore-funds-self-assessment-helpsheet-hs265/hs265-offshore-funds

        Example of UK offshore funds are the most common UCITS ETFs (Vanguard,
        Blackrock, XTrackers) that are normally located in Ireland.

        When those funds are "reporting" funds, that is, enlisted in HMRC
        official list of reporting funds:
        https://www.gov.uk/government/publications/offshore-funds-list-of-reporting-funds
        We need to declare the excess income periodically (yearly) from these
        funds.

        Excess Reported Income (ERI) is all the income reported by the fund
        not distributed to you (normally through dividends).
        Note that both Accumulating and Distributing funds can have reportable
        income and require reporting.

        The ERI is calculated based on the number shares owned at the end of
        the fund end reporting day for each fund.
        You multiply number of shares times the Reportable income amount per
        share as reported by each fund.

        Fund reports are directly provided in the fund website (i.e. Blackrock,
        Vanguard, XTrackers, etc) on a yearly fashion.

        The ERI has two consequences:

        1) It increases your share cost basis at the time it materializes.
        2) It represents taxable income (either as dividend or interest
           depending on the fund type) at a future date, exactly 6 calendar
           months since the reporting day.

        Note that ERI also takes into account Bed and Breakfast so you're due
        ERI even if you sell before the reporting day and buy within 30 days.
        See https://www.rawknowledge.ltd/eri-explained-four-tricky-questions-answered/

        For some calculation example beside HMRC website you can use Vanguard
        FAQ:
        https://www.vanguardinvestor.co.uk/content/dam/intl/uk-retail-direct/general/uk-reporting-fund-faq.pdf

        Note that the current implementation doesn't take into account
        equalisation strategy which is an optional fund reporting feature that
        allows for pro rata reporting when you buy the fund shares within a
        reporting period.

        """
        distribution_date = transaction.date + ERI_TAX_DATE_DELTA

        assert transaction.isin is not None, f"{transaction} doesn't have a valid ISIN"
        assert transaction.price is not None, (
            f"{transaction} doesn't have a valid price"
        )

        if transaction.price == Decimal(0):
            return

        price = self.currency_converter.to_gbp_for(
            transaction.price,
            transaction,
            LOGGER
        )

        symbols = self.isin_converter.get_symbols(transaction.isin)
        for symbol in symbols:
            for report_date, report_by_symbol in self.eris.items():
                if symbol in report_by_symbol and report_date == transaction.date:
                    previous_price = report_by_symbol[symbol].price
                    if approx_equal(previous_price, price):
                        LOGGER.warning(
                            "Skipping duplicated ERI transaction: %s", transaction
                        )
                        return
                    raise InvalidTransactionError(
                        transaction,
                        f"A conflicting ERI report at {report_date} for "
                        f"{symbol} of £{price} has been found at "
                        f"{report_date} of £{previous_price}",
                    )

            self.eris[transaction.date][symbol] = ExcessReportedIncome(
                price=price,
                symbol=symbol,
                date=transaction.date,
                distribution_date=distribution_date,
                is_interest=symbol in self.interest_fund_tickers,
            )

    def convert_to_hmrc_transactions(
        self,
        transactions: list[BrokerTransaction],
    ) -> None:
        """Convert broker transactions to HMRC transactions."""
        # We keep a balance per broker,currency pair
        balance: dict[tuple[str, str], Decimal] = defaultdict(lambda: Decimal(0))
        dividends: dict[tuple[str, str], Decimal] = defaultdict(Decimal)
        dividends_tax: dict[tuple[str, str], Decimal] = defaultdict(Decimal)
        interests: dict[tuple[str, str], Decimal] = defaultdict(Decimal)
        total_disposal_proceeds = Decimal(0)
        balance_history: list[Decimal] = []

        for transaction in transactions:
            self.isin_converter.add_from_transaction(transaction)

        for i, transaction in enumerate(transactions):
            if transaction.broker != 'N/A':

                try:
                    self.mixed_funds[transaction.broker]
                except KeyError:
                    self.mixed_funds[transaction.broker] = MixedFund(transaction.broker)

                self.mixed_funds[transaction.broker].add(transaction)

            if transaction.action == ActionType.EXCESS_REPORTED_INCOME:
                self.add_eri(transaction)
                balance_history.append(
                    Decimal(0)
                )  # dummy value, this will get filtered out
                continue
            new_balance = balance[(transaction.broker, transaction.currency)]
            if transaction.action in [
                ActionType.BUY_OPTION,
                ActionType.SELL_OPTION,
                ActionType.EXPIRATION
            ]:
                transaction.quantity = 100 * transaction.quantity
            if transaction.action ==ActionType.EXPIRATION:
                transaction.quantity = -transaction.quantity
                transaction.amount = 0
                transaction.price = 0
            if transaction.action is ActionType.TRANSFER:
                new_balance += get_amount_or_fail(transaction)
            elif transaction.action in [
                ActionType.BUY,
                ActionType.BUY_OPTION,
                ActionType.REINVEST_SHARES,
            ]:
                new_balance += get_amount_or_fail(transaction)
                self.add_acquisition(transaction)
            elif transaction.action in [
                ActionType.SELL,
                ActionType.CASH_MERGER,
                ActionType.FULL_REDEMPTION,
                ActionType.SELL_OPTION,
                ActionType.EXPIRATION,
            ]:
                amount = get_amount_or_fail(transaction)
                new_balance += amount

                self.add_disposal(transaction)
                if self.date_in_tax_year(transaction.date):
                    total_disposal_proceeds += self.currency_converter.to_gbp_for(
                        amount + transaction.fees, transaction, LOGGER
                    )
            elif transaction.action is ActionType.FEE:
                amount = get_amount_or_fail(transaction)
                new_balance += amount
            elif transaction.action in [
                ActionType.STOCK_ACTIVITY,
                ActionType.SPIN_OFF,
            ]:
                self.add_acquisition(transaction)
            elif transaction.action in [
                ActionType.STOCK_SPLIT,
            ]:
                # Calculate the multiplier based on portfolio and received shares
                acquired_quantity = get_quantity_or_fail(transaction)
                symbol = get_symbol_or_fail(transaction)
                holding_quantity = self.portfolio[symbol].quantity
                multiplier = (acquired_quantity + holding_quantity) / holding_quantity
                self.split_list[(symbol, transaction.date)] = multiplier
                self.add_acquisition(transaction)
            elif transaction.action in [
                    ActionType.STOCK_REVERSE_SPLIT,
                ]:
                # Assumes a reverse split where fractional shares are awarded to round to next whole share
                # Assumes a bookkeeping transaction with -N transaction & a positive transaction CEILING(N/30)

                if transaction.quantity < 0:
                    # This is the bookkeeping transaction
                    pass
                else:
                    new_quantity = get_quantity_or_fail(transaction)
                    symbol = get_symbol_or_fail(transaction)
                    holding_quantity = self.portfolio[symbol].quantity
                    multiplier = new_quantity / holding_quantity
                    self.split_list[(symbol, transaction.date)] = multiplier

                    disposed_quantity = holding_quantity - new_quantity
                    transaction.quantity = disposed_quantity
                    transaction.price = 0
                    transaction.amount = 0
                    self.add_disposal(transaction)


            elif transaction.action in [ActionType.DIVIDEND, ActionType.CAPITAL_GAIN]:
                amount = get_amount_or_fail(transaction)
                symbol = get_symbol_or_fail(transaction)
                currency = transaction.currency
                new_balance += amount
                self.dividend_list[(symbol, transaction.date)] += ForeignCurrencyAmount(
                    amount, currency
                )
                if self.date_in_tax_year(transaction.date):
                    dividends[(symbol, currency)] += amount
            elif transaction.action is ActionType.NRA_TAX_ADJ and transaction.symbol:
                amount = get_amount_or_fail(transaction)
                symbol = get_symbol_or_fail(transaction)
                currency = transaction.currency
                new_balance += amount
                self.dividend_tax_list[(symbol, transaction.date)] += (
                    ForeignCurrencyAmount(amount, currency)
                )
                if self.date_in_tax_year(transaction.date):
                    dividends_tax[(symbol, currency)] += amount
            elif transaction.action is ActionType.ADJUSTMENT:
                amount = get_amount_or_fail(transaction)
                new_balance += amount
            elif transaction.action == ActionType.INTEREST or transaction.action == ActionType.NRA_TAX_ADJ and transaction.symbol is None:
                amount = get_amount_or_fail(transaction)
                new_balance += amount
                self.interest_list[
                    (transaction.broker, transaction.currency, transaction.date)
                ] += ForeignCurrencyAmount(amount, transaction.currency)
                if self.date_in_tax_year(transaction.date):
                    interests[(transaction.broker, transaction.currency)] += amount
            elif transaction.action is ActionType.WIRE_FUNDS_RECEIVED:
                amount = get_amount_or_fail(transaction)
                new_balance += amount
            elif transaction.action is ActionType.REINVEST_DIVIDENDS:
                LOGGER.warning("Ignoring unsupported action: %s", transaction.action)
            elif transaction.action == ActionType.BOOKKEEPING:
                pass
            else:
                raise InvalidTransactionError(
                    transaction, f"Action not processed({transaction.action})"
                )
            balance_history.append(new_balance)
            if self.balance_check and new_balance < 0:
                msg = f"Reached a negative balance({new_balance})"
                msg += f" for broker {transaction.broker} ({transaction.currency})"
                msg += " after processing the following transactions:\n"
                msg += (
                    "\n".join(
                        [
                            f"{trx}\nBalance after transaction={balance_after}"
                            for trx, balance_after in zip(
                                transactions[: i + 1], balance_history, strict=True
                            )
                            # filter out ERI transactions, they don't affect the balance
                            if trx.action != ActionType.EXCESS_REPORTED_INCOME
                        ]
                    )
                    + "\n"
                )
                msg += "Tip: If your input file is missing deposits/withdrawals use --no-balance-check."
                raise CalculationError(msg)
            balance[(transaction.broker, transaction.currency)] = new_balance

        self.first_pass_report(
            balance, dividends, dividends_tax, interests, total_disposal_proceeds
        )

    def preprocess_mixed_fund(self, broker: str) -> None:
        """Prepares the raw transactions of a mixed fund so that they are ready to be browsed for mixed fund calc:
        Amount is converted to GBP as of the date of the transaction

        * Dividends are matched with their respective tax event, if any
        * Interests are matched with their respective tax event, if any
        * Stock activity is matched with their respective OWR event, if any
        * Transfers in/out are matched with their origin/destination

        """

        mixed_fund = self.mixed_funds[broker]
        mixed_fund.preprocessed_mixed_fund_transaction_log = []

        dividend_tax_transactions = [transaction for transaction in mixed_fund.mixed_fund_transaction_log \
                                     if transaction.action == ActionType.NRA_TAX_ADJ and transaction.symbol]
        interest_tax_transactions = [transaction for transaction in mixed_fund.mixed_fund_transaction_log \
                                     if transaction.action == ActionType.NRA_TAX_ADJ and  transaction.symbol is None]

        for transaction in mixed_fund.mixed_fund_transaction_log:
            if transaction.action == ActionType.DIVIDEND:
                # Dividends need to be matched to their possible tax event
                dividend_tax_transaction = transaction.find_close_event(
                    [tax for tax in dividend_tax_transactions if tax.symbol == transaction.symbol],
                    min_delta=0, max_delta=0)

                processed_mixed_fund_transaction = ProcessedMixedFundTransaction(
                    broker=transaction.broker,
                    date=transaction.date,
                    action=transaction.action,
                    amount=self.currency_converter.to_gbp_for(transaction.amount, transaction),
                    fees=self.currency_converter.to_gbp_for(transaction.fees, transaction),
                    symbol=transaction.symbol,
                    tax_at_source=self.currency_converter.to_gbp_for(dividend_tax_transaction.amount, dividend_tax_transaction) if dividend_tax_transaction else 0
                )
                mixed_fund.processed_mixed_fund_transaction_log.append(processed_mixed_fund_transaction)
            if transaction.action == ActionType.INTEREST:
                # Interests need to be matched to their possible tax event
                interest_tax_transaction = transaction.find_close_event(interest_tax_transactions,
                    min_delta=0, max_delta=0)

                processed_mixed_fund_transaction = ProcessedMixedFundTransaction(
                    broker=transaction.broker,
                    date=transaction.date,
                    action=transaction.action,
                    amount=self.currency_converter.to_gbp_for(transaction.amount, transaction),
                    fees=self.currency_converter.to_gbp_for(transaction.fees, transaction),
                    tax_at_source=self.currency_converter.to_gbp_for(interest_tax_transaction.amount, interest_tax_transaction) if interest_tax_transaction else 0
                )
                mixed_fund.processed_mixed_fund_transaction_log.append(processed_mixed_fund_transaction)

            if transaction.action == ActionType.STOCK_ACTIVITY:
                # Stock activity is matched to the OWR events tables to figure out the OWR rate
                owr_event = transaction.find_close_event(
                    [owr_event for owr_event in self.owr_events if (owr_event.broker == transaction.broker
                                                                    and owr_event.symbol == transaction.symbol
                                                                    and owr_event.quantity == transaction.pre_tax_quantity
                                                                    )
                    ],
                    min_delta=6, max_delta=0)

                if not owr_event:
                    raise InvalidTransactionError(transaction, message="Couldn't find a matching OWR event for this stock award activity")

                owr_rate = (
                    owr_event.overseas_working_days
                    / owr_event.working_days
                    * owr_event.vesting_days_in_three_years
                    / owr_event.vesting_days
                ) if owr_event.working_days != 0 else Decimal(0)

                processed_mixed_fund_transaction = ProcessedMixedFundTransaction(
                    broker=transaction.broker,
                    date=transaction.date,
                    action=transaction.action,
                    quantity=transaction.quantity,
                    fees=self.currency_converter.to_gbp_for(transaction.fees, transaction),
                    price=self.currency_converter.to_gbp_for(transaction.price, transaction),
                    symbol=transaction.symbol,
                    owr_rate=owr_rate,
                    pre_tax_quantity=transaction.pre_tax_quantity
                )
                mixed_fund.processed_mixed_fund_transaction_log.append(processed_mixed_fund_transaction)

            if transaction.action in [ActionType.TRANSFER, ActionType.WIRE_FUNDS_RECEIVED, ActionType.FEE, ActionType.ADJUSTMENT]:
                processed_mixed_fund_transaction = ProcessedMixedFundTransaction(
                    broker=transaction.broker,
                    date=transaction.date,
                    action=transaction.action,
                    amount=self.currency_converter.to_gbp_for(transaction.amount, transaction),
                    fees=self.currency_converter.to_gbp_for(transaction.fees, transaction),
                    destination=transaction.destination if transaction.action == ActionType.TRANSFER else None,
                    origin=transaction.origin if transaction.action == ActionType.WIRE_FUNDS_RECEIVED else None
                )
                mixed_fund.processed_mixed_fund_transaction_log.append(processed_mixed_fund_transaction)

            if transaction.action == ActionType.SELL:
                processed_mixed_fund_transaction = ProcessedMixedFundTransaction(
                    broker=transaction.broker,
                    date=transaction.date,
                    action=transaction.action,
                    amount=self.currency_converter.to_gbp_for(transaction.amount, transaction),
                    quantity=transaction.quantity,
                    fees=self.currency_converter.to_gbp_for(transaction.fees, transaction),
                    symbol=transaction.symbol,
                    price=self.currency_converter.to_gbp_for(transaction.price, transaction)
                )
                mixed_fund.processed_mixed_fund_transaction_log.append(processed_mixed_fund_transaction)

    def preprocess_mixed_funds(self) -> None:
        """Pre-process all the mixed funds"""
        for broker in self.mixed_funds.keys():
            self.preprocess_mixed_fund(broker)


    def first_pass_report(
        self,
        balance: dict[tuple[str, str], Decimal],
        dividends: dict[tuple[str, str], Decimal],
        dividends_tax: dict[tuple[str, str], Decimal],
        interests: dict[tuple[str, str], Decimal],
        total_disposal_proceeds: Decimal,
    ) -> None:
        """Print the results of the first pass."""
        print("First pass completed")
        print("Final portfolio:")
        for stock, position in self.portfolio.items():
            print(f"  {stock}: {position}")
        print("Final balance:")
        for (broker, currency), amount in balance.items():
            print(f"  {broker}: {round_decimal(amount, 2)} ({currency})")
        if dividends:
            print("Dividends:")
            for (symbol, currency), amount in dividends.items():
                tax = dividends_tax[(symbol, currency)]
                tax_str = f", excluding {-tax} taxed at source" if tax < 0 else ""
                print(f"  {symbol}: {round_decimal(amount, 2)}{tax_str} ({currency})")
        if interests:
            print("Interests:")
            for (broker, currency), amount in interests.items():
                print(f"  {broker}: {round_decimal(amount, 2)} ({currency})")
        print(f"Disposal proceeds: £{round_decimal(total_disposal_proceeds, 2)}")
        print()

    def process_acquisition(
        self,
        symbol: str,
        date_index: datetime.date,
    ) -> list[CalculationEntry]:
        """Process single acquisition."""
        acquisition = self.acquisition_list[date_index][symbol]
        modified_amount = acquisition.amount
        position = self.portfolio[symbol]
        calculation_entries = []
        # Management fee transaction can have 0 quantity
        assert acquisition.quantity >= 0
        # Stock split can have 0 amount
        assert acquisition.amount >= 0

        bnb_acquisition = HmrcTransactionData()
        bed_and_breakfast_fees = Decimal(0)

        # if acquisition matches an OWR event:
        #     update the mixed fund status

        if acquisition.quantity > 0 and has_key(self.bnb_list, date_index, symbol):
            acquisition_price = acquisition.amount / acquisition.quantity
            bnb_acquisition = self.bnb_list[date_index][symbol]
            assert bnb_acquisition.quantity <= acquisition.quantity
            modified_amount -= bnb_acquisition.quantity * acquisition_price
            modified_amount += bnb_acquisition.amount
            assert modified_amount > 0
            bed_and_breakfast_fees = (
                acquisition.fees * bnb_acquisition.quantity / acquisition.quantity
            )
            calculation_entries.append(
                CalculationEntry(
                    rule_type=RuleType.BED_AND_BREAKFAST,
                    quantity=bnb_acquisition.quantity,
                    amount=-bnb_acquisition.amount,
                    new_quantity=position.quantity + bnb_acquisition.quantity,
                    new_pool_cost=position.amount + bnb_acquisition.amount,
                    fees=bed_and_breakfast_fees,
                    allowable_cost=acquisition.amount,
                    eris=bnb_acquisition.eris,
                )
            )
        self.portfolio[symbol] += Position(
            acquisition.quantity,
            modified_amount,
        )
        LOGGER.debug(
            "Acquisition on %s of %s: quantity %d for cost £%.2f (£%.2f per share). Section 104: quantity %d for total cost: £%.2f (£%.2f per share)",
            date_index,
            symbol,
            acquisition.quantity,
            acquisition.amount,
            acquisition.amount / acquisition.quantity,
            self.portfolio[symbol].quantity,
            self.portfolio[symbol].amount,
            self.portfolio[symbol].amount / self.portfolio[symbol].quantity
        )
        if (
            acquisition.quantity - bnb_acquisition.quantity > 0
            or bnb_acquisition.quantity == 0
        ):
            spin_off = next(
                (
                    spin_off
                    for spin_off in self.spin_offs[date_index]
                    if spin_off.dest == symbol
                ),
                None,
            )
            calculation_entries.append(
                CalculationEntry(
                    rule_type=RuleType.SECTION_104,
                    quantity=acquisition.quantity - bnb_acquisition.quantity,
                    amount=-(modified_amount - bnb_acquisition.amount),
                    new_quantity=position.quantity + acquisition.quantity,
                    new_pool_cost=position.amount + modified_amount,
                    fees=acquisition.fees - bed_and_breakfast_fees,
                    allowable_cost=acquisition.amount,
                    spin_off=spin_off,
                )
            )
        return calculation_entries

    def process_disposal(
        self,
        symbol: str,
        date_index: datetime.date,
    ) -> tuple[Decimal, list[CalculationEntry], CalculationEntry | None]:
        """Process single disposal."""
        disposal = self.disposal_list[date_index][symbol]
        disposal_quantity = disposal.quantity
        proceeds_amount = disposal.amount
        original_disposal_quantity = disposal_quantity
        disposal_price = proceeds_amount / disposal_quantity
        current_quantity = self.portfolio[symbol].quantity
        spin_off_entry = None

        for date, spin_offs in self.spin_offs.items():
            if date > date_index:
                continue
            for spin_off in spin_offs:
                # Up to the actual spin-off happening all the sales has to happen based
                # on original cost basis, after spin-off we have to consider its impact
                # for all future trades
                amount = self.portfolio[spin_off.source].amount
                quantity = self.portfolio[spin_off.source].quantity
                new_amount = amount * spin_off.cost_proportion
                LOGGER.debug(
                    "Detected spin-off of %s to %s on %s, modyfing the cost amount "
                    "from %d to %d according to cost-proportion: %.2f",
                    spin_off.source,
                    spin_off.dest,
                    spin_off.date,
                    amount,
                    new_amount,
                    spin_off.cost_proportion,
                )
                self.spin_offs[date] = spin_offs[1:]
                self.portfolio[spin_off.source].amount = new_amount
                spin_off_entry = CalculationEntry(
                    RuleType.SPIN_OFF,
                    quantity=quantity,
                    amount=-amount,
                    new_quantity=quantity,
                    gain=None,
                    # Fees, if any are already accounted on the acquisition of
                    # spined off shares
                    fees=Decimal(0),
                    new_pool_cost=new_amount,
                    allowable_cost=new_amount,
                    spin_off=spin_off,
                )

        current_amount = self.portfolio[symbol].amount
        assert disposal_quantity <= current_quantity
        chargeable_gain = Decimal(0)
        calculation_entries = []
        # Same day rule is first
        if has_key(self.acquisition_list, date_index, symbol):
            same_day_acquisition = self.acquisition_list[date_index][symbol]

            available_quantity = min(disposal_quantity, same_day_acquisition.quantity)
            if available_quantity > 0:
                fees = disposal.fees * available_quantity / original_disposal_quantity
                acquisition_price = (
                    same_day_acquisition.amount / same_day_acquisition.quantity
                )
                same_day_amount = available_quantity * disposal_price
                same_day_proceeds = same_day_amount + fees
                same_day_allowable_cost = available_quantity * acquisition_price + fees
                same_day_gain = same_day_proceeds - same_day_allowable_cost
                chargeable_gain += same_day_gain
                LOGGER.debug(
                    "Disposal SAME DAY on %s of %s: quantity %d for proceeds £%.2f (disposal price: £%.2f per share). Generated gain £%.2f as same day cost was £%.2f (£%.2f per share) ",
                    date_index,
                    symbol,
                    available_quantity,
                    same_day_proceeds,
                    disposal_price,
                    same_day_gain,
                    same_day_allowable_cost,
                    acquisition_price,
                )
                disposal_quantity -= available_quantity
                proceeds_amount -= available_quantity * disposal_price
                current_quantity -= available_quantity
                # These shares shouldn't be added to Section 104 holding
                current_amount -= available_quantity * acquisition_price
                if current_quantity == 0:
                    assert round_decimal(current_amount, 23) == 0, (
                        f"current amount {current_amount}"
                    )
                calculation_entries.append(
                    CalculationEntry(
                        rule_type=RuleType.SAME_DAY,
                        quantity=available_quantity,
                        amount=same_day_amount,
                        gain=same_day_gain,
                        allowable_cost=same_day_allowable_cost,
                        fees=fees,
                        new_quantity=current_quantity,
                        new_pool_cost=current_amount,
                    )
                )

        # Bed and breakfast rule next
        if disposal_quantity > 0:
            eris = []
            eri = self.get_eri(symbol, date_index)
            if eri:
                eris.append(eri)

            split_multiplier = Decimal(1)

            for i in range(BED_AND_BREAKFAST_DAYS):
                search_index = date_index + datetime.timedelta(days=i + 1)

                # Check if there was any stock split, in which case we need to adjust the B&D quantity
                split_multiplier *= self.split_list.get(
                    (symbol, search_index), Decimal(1)
                )

                # ERI are distributed annually but when a fund close we might have
                # multiple ERI distribution in close succession
                eri = self.get_eri(symbol, search_index)
                if eri:
                    eris.append(eri)
                if has_key(self.acquisition_list, search_index, symbol):
                    acquisition = self.acquisition_list[search_index][symbol]

                    bnb_acquisition = (
                        self.bnb_list[search_index][symbol]
                        if has_key(self.bnb_list, search_index, symbol)
                        else HmrcTransactionData()
                    )
                    assert bnb_acquisition.quantity <= acquisition.quantity

                    same_day_disposal = (
                        self.disposal_list[search_index][symbol]
                        if has_key(self.disposal_list, search_index, symbol)
                        else HmrcTransactionData()
                    )
                    if same_day_disposal.quantity > acquisition.quantity:
                        # If the number of shares disposed of exceeds the number
                        # acquired on the same day the excess shares will be identified
                        # in the normal way.
                        continue

                    # This can be some management fee entry or already used
                    # by bed and breakfast rule
                    if (
                        acquisition.quantity
                        - same_day_disposal.quantity
                        - bnb_acquisition.quantity
                        == 0
                    ):
                        continue
                    # Splits are the only transaction that receive shares for free
                    # they can't be part of a B&B
                    if acquisition.amount == 0:
                        LOGGER.warning(
                            "A split happened shortly after a disposal of %s, double check these transactions."
                            "Disposed on %s and split happened on %s",
                            symbol,
                            date_index,
                            search_index,
                        )
                        continue
                    LOGGER.warning(
                        "Bed and breakfasting for %s. "
                        "Disposed on %s and acquired again on %s",
                        symbol,
                        date_index,
                        search_index,
                    )
                    if split_multiplier != Decimal(1):
                        LOGGER.warning(
                            "Bed & breakfast for %s is taking into account a {%.2f}x split "
                            "that happened shortly before the repurchase of shares",
                            symbol,
                            split_multiplier,
                        )
                    available_quantity = min(
                        disposal_quantity,
                        acquisition.quantity / split_multiplier
                        - same_day_disposal.quantity
                        - bnb_acquisition.quantity,
                    )
                    fees = (
                        disposal.fees * available_quantity / original_disposal_quantity
                    )
                    acquisition_price = acquisition.amount / (
                        acquisition.quantity / split_multiplier
                    )
                    bed_and_breakfast_amount = available_quantity * disposal_price
                    bed_and_breakfast_proceeds = bed_and_breakfast_amount + fees
                    bed_and_breakfast_allowable_cost = (
                        available_quantity * acquisition_price
                    ) + fees
                    # ERI needs to be reported when doing bed and breakfast as if you
                    # held the stocks at the reporting end date.
                    # https://www.rawknowledge.ltd/eri-explained-four-tricky-questions-answered/
                    total_dist_amount = Decimal(0)
                    for eri in eris:
                        eri_distribution = ExcessReportedIncomeDistribution(
                            price=eri.price,
                            amount=available_quantity * eri.price,
                            quantity=available_quantity,
                        )
                        total_dist_amount += eri_distribution.amount
                        if self.date_in_tax_year(eri.distribution_date):
                            self.eris_distribution[eri.distribution_date][symbol] += (
                                eri_distribution
                            )

                    bed_and_breakfast_gain = (
                        bed_and_breakfast_proceeds - bed_and_breakfast_allowable_cost
                    )
                    chargeable_gain += bed_and_breakfast_gain
                    LOGGER.debug(
                        "Disposal BED & BREAKFAST on %s of %s: quantity %d for proceeds £%.2f (disposal price: £%.2f per share). Generated gain £%.2f as B&B cost was £%.2f (£%.2f per share) %s",
                        date_index,
                        symbol,
                        available_quantity,
                        bed_and_breakfast_proceeds,
                        disposal_price,
                        bed_and_breakfast_gain,
                        bed_and_breakfast_allowable_cost,
                        acquisition_price,
                        f", added_excess_income: {total_dist_amount}"
                        if total_dist_amount > 0
                        else "",
                    )
                    disposal_quantity -= available_quantity
                    proceeds_amount -= available_quantity * disposal_price
                    current_price = current_amount / current_quantity
                    amount_delta = available_quantity * current_price
                    current_quantity -= available_quantity
                    current_amount -= amount_delta
                    if current_quantity == 0:
                        assert round_decimal(current_amount, 23) == 0, (
                            f"current amount {current_amount}"
                        )
                    add_to_list(
                        self.bnb_list,
                        search_index,
                        symbol,
                        available_quantity * split_multiplier,
                        amount_delta + total_dist_amount,
                        Decimal(0),
                        eris,
                    )
                    calculation_entries.append(
                        CalculationEntry(
                            rule_type=RuleType.BED_AND_BREAKFAST,
                            quantity=available_quantity,
                            amount=bed_and_breakfast_amount,
                            gain=bed_and_breakfast_gain,
                            allowable_cost=bed_and_breakfast_allowable_cost,
                            fees=fees,
                            bed_and_breakfast_date_index=search_index,
                            new_quantity=current_quantity,
                            new_pool_cost=current_amount,
                        )
                    )
                    # If we completely matched the current disposal,
                    # there's no need to keep looking for more B&D days
                    if disposal_quantity <= 0:
                        break
        if disposal_quantity > 0:
            available_quantity = disposal_quantity
            fees = disposal.fees * available_quantity / original_disposal_quantity
            acquisition_price = current_amount / current_quantity
            r104_amount = available_quantity * disposal_price
            r104_proceeds = r104_amount + fees
            r104_allowable_cost = available_quantity * acquisition_price + fees
            r104_gain = r104_proceeds - r104_allowable_cost
            chargeable_gain += r104_gain
            LOGGER.debug(
                "Disposal SECTION 104 on %s of %s: quantity %d for proceeds £%.2f (disposal price: £%.2f per share). Generated gain £%.2f as section 104 cost was £%.2f (£%.2f per share)",
                date_index,
                symbol,
                available_quantity,
                r104_proceeds,
                disposal_price,
                r104_gain,
                r104_allowable_cost,
                acquisition_price,
            )
            disposal_quantity -= available_quantity
            proceeds_amount -= available_quantity * disposal_price
            current_price = current_amount / current_quantity
            amount_delta = available_quantity * current_price
            current_quantity -= available_quantity
            current_amount -= amount_delta
            if current_quantity == 0:
                assert round_decimal(current_amount, 10) == 0, (
                    f"current amount {current_amount}"
                )
            calculation_entries.append(
                CalculationEntry(
                    rule_type=RuleType.SECTION_104,
                    quantity=available_quantity,
                    amount=r104_amount,
                    gain=r104_gain,
                    allowable_cost=r104_allowable_cost,
                    fees=fees,
                    new_quantity=current_quantity,
                    new_pool_cost=current_amount,
                )
            )
            disposal_quantity = Decimal(0)

        assert round_decimal(disposal_quantity, 23) == 0, (
            f"disposal quantity {disposal_quantity}"
        )
        self.portfolio[symbol] = Position(current_quantity, current_amount)
        chargeable_gain = round_decimal(chargeable_gain, 2)

        # if disposal:
        #     update the mixed fund status (add gains)

        return (
            chargeable_gain,
            calculation_entries,
            spin_off_entry,
        )

    def process_eri(
        self,
        symbol: str,
        date_index: datetime.date,
    ) -> CalculationEntry | None:
        """Process single excess reported income."""
        eri = self.get_eri(symbol, date_index)
        assert eri is not None
        amount = self.portfolio[eri.symbol].amount
        quantity = self.portfolio[eri.symbol].quantity

        if quantity == 0:
            return None

        allowable_cost = quantity * eri.price

        if allowable_cost == 0:
            return None

        new_amount = amount + allowable_cost
        LOGGER.debug(
            "Detected excess reported income of %s on %s, "
            "modyfing the cost amount from %d to %d",
            eri.symbol,
            eri.date,
            amount,
            new_amount,
        )
        self.portfolio[eri.symbol].amount = new_amount

        if self.date_in_tax_year(eri.distribution_date):
            self.eris_distribution[eri.distribution_date][symbol] += (
                ExcessReportedIncomeDistribution(
                    price=eri.price,
                    amount=allowable_cost,
                    quantity=quantity,
                )
            )

        return CalculationEntry(
            RuleType.EXCESS_REPORTED_INCOME,
            quantity=quantity,
            amount=-amount,
            new_quantity=quantity,
            gain=None,
            fees=Decimal(0),
            new_pool_cost=new_amount,
            allowable_cost=allowable_cost,
            eris=[eri],
        )

    def process_interests(self) -> None:
        """Process all interest events.

        It groups them by month, using the last date on each month for the report
        and updates the interest totals for the year.
        """
        monthly_interests: dict[
            tuple[str, str, datetime.date], ForeignCurrencyAmount
        ] = defaultdict(ForeignCurrencyAmount)
        last_date: datetime.date = datetime.date.min
        last_broker: str | None = None
        last_currency: str | None = None

        for (broker, currency, date), foreign_amount in sorted(
            self.interest_list.items()
        ):
            if self.date_in_tax_year(date):
                if (
                    broker == last_broker
                    and date.month == last_date.month
                    and currency == last_currency
                ):
                    monthly_interests[(broker, currency, date)] = monthly_interests.pop(
                        (broker, currency, last_date)
                    )
                monthly_interests[(broker, currency, date)] += foreign_amount
                last_date = date
                last_broker = broker
                last_currency = currency

        for (broker, currency, date), foreign_amount in monthly_interests.items():
            gbp_amount = self.currency_converter.to_gbp(
                foreign_amount.amount, foreign_amount.currency, date, LOGGER
            )
            if foreign_amount.currency == UK_CURRENCY:
                self.total_uk_interest += gbp_amount
                rule_prefix = "interestUK"
            else:
                self.total_foreign_interest += gbp_amount
                rule_prefix = f"interest{currency.upper()}"

            self.calculation_log_yields[date][f"{rule_prefix}${broker}"] = [
                CalculationEntry(
                    rule_type=RuleType.INTEREST,
                    quantity=Decimal(1),
                    amount=gbp_amount,
                    new_quantity=Decimal(1),
                    new_pool_cost=Decimal(0),
                    fees=Decimal(0),
                )
            ]

    def process_dividends(self) -> None:
        """Process all dividends events and taxes.

        It updates the interest total for the year if needed.
        """
        for (symbol, date), foreign_amount in self.dividend_list.items():
            tax = self.dividend_tax_list[(symbol, date)]

            treaty = None
            is_interest_fund = symbol in self.interest_fund_tickers
            if tax.amount < 0:
                if is_interest_fund:
                    LOGGER.warning(
                        "Cannot apply taxation treaty for bond fund %s", symbol
                    )
                elif foreign_amount.currency != UK_CURRENCY:
                    assert tax.currency == foreign_amount.currency, (
                        f"Not matching currency for dividend {foreign_amount.currency} "
                        f"and its tax {tax.currency}"
                    )
                    try:
                        treaty = DIVIDEND_DOUBLE_TAXATION_RULES[foreign_amount.currency]
                    except KeyError:
                        LOGGER.warning(
                            "Taxation treaty for %s country is missing (ticker: %s), "
                            "double taxation rules cannot be determined!",
                            foreign_amount.currency,
                            symbol,
                        )
                        treaty = None
                    else:
                        assert treaty is not None
                        expected_tax = treaty.country_rate * -foreign_amount.amount
                        if not approx_equal(expected_tax, tax.amount):
                            LOGGER.warning(
                                "Determined double taxation treaty does not match the "
                                "base taxation rules (expected %.2f base tax for %s "
                                "but %.2f was deducted) for %s ticker!",
                                expected_tax,
                                treaty.country,
                                tax.amount,
                                symbol,
                            )
                            treaty = None

            amount = self.currency_converter.to_gbp(
                foreign_amount.amount, foreign_amount.currency, date, LOGGER
            )
            tax_amount = self.currency_converter.to_gbp(
                tax.amount, foreign_amount.currency, date, LOGGER
            )

            if self.date_in_tax_year(date):
                dividend = Dividend(
                    date=date,
                    symbol=symbol,
                    amount=amount,
                    tax_at_source=tax_amount,
                    is_interest=is_interest_fund,
                    tax_treaty=treaty,
                )

                self.calculation_log_yields[date][f"dividend${symbol}"] = [
                    CalculationEntry(
                        rule_type=RuleType.DIVIDEND,
                        quantity=Decimal(1),
                        amount=amount,
                        new_quantity=Decimal(1),
                        new_pool_cost=Decimal(0),
                        fees=Decimal(0),
                        dividend=dividend,
                    )
                ]

                if is_interest_fund:
                    self.total_foreign_interest += amount

    def calculate_capital_gain(
        self,
    ) -> CapitalGainsReport:
        """Calculate capital gain and return generated report."""
        begin_index = INTERNAL_START_DATE
        tax_year_start_index = self.tax_year_start_date
        end_index = self.tax_year_end_date
        disposal_count = 0
        disposed_symbols = set()
        disposal_proceeds = Decimal(0)
        allowable_costs = Decimal(0)
        capital_gain = Decimal(0)
        capital_loss = Decimal(0)
        self.portfolio.clear()

        calculation_log: CalculationLog = defaultdict(dict)
        all_sales_log: CalculationLog = defaultdict(dict)

        mixed_funds_log = dict()

        for broker in self.mixed_funds.keys():
            mixed_funds_log[broker] = []

        for date_index in (
            begin_index + datetime.timedelta(days=x)
            for x in range((end_index - begin_index).days + 1)
        ):
            if date_index in self.acquisition_list:
                for symbol in self.acquisition_list[date_index]:
                    calculation_entries = self.process_acquisition(
                        symbol,
                        date_index,
                    )
                    if date_index >= tax_year_start_index:
                        calculation_log[date_index][f"buy${symbol}"] = (
                            calculation_entries
                        )
            if date_index in self.disposal_list:
                for symbol in self.disposal_list[date_index]:
                    (
                        transaction_capital_gain,
                        calculation_entries,
                        spin_off_entry,
                    ) = self.process_disposal(
                        symbol,
                        date_index,
                    )

                    transaction_amount = self.disposal_list[date_index][
                        symbol
                    ].amount
                    transaction_fees = self.disposal_list[date_index][symbol].fees
                    transaction_disposal_proceeds = (
                        transaction_amount + transaction_fees
                    )
                    transaction_quantity = self.disposal_list[date_index][
                        symbol
                    ].quantity

                    calculated_quantity = Decimal(0)
                    calculated_proceeds = Decimal(0)
                    calculated_gain = Decimal(0)
                    for entry in calculation_entries:
                        calculated_quantity += entry.quantity
                        calculated_proceeds += entry.amount + entry.fees
                        calculated_gain += entry.gain
                    assert transaction_quantity == calculated_quantity
                    assert round_decimal(
                        transaction_disposal_proceeds, 10
                    ) == round_decimal(calculated_proceeds, 10), (
                        f"{transaction_disposal_proceeds} != {calculated_proceeds}"
                    )
                    assert transaction_capital_gain == round_decimal(
                        calculated_gain, 2
                    )

                    all_sales_log[date_index][f"sell${symbol}"] = (
                        calculation_entries
                    )

                    if date_index >= tax_year_start_index:
                        disposal_count += 1
                        disposed_symbols.add(symbol)
                        disposal_proceeds += transaction_disposal_proceeds
                        allowable_costs += (
                            transaction_disposal_proceeds - transaction_capital_gain
                        )

                        LOGGER.debug(
                            "[TAX YEAR CGT EVENT] Disposal on %s of %s, quantity %d leads to capital gain £%s",
                            date_index,
                            symbol,
                            transaction_quantity,
                            round_decimal(transaction_capital_gain, 2),
                        )

                        calculation_log[date_index][f"sell${symbol}"] = (
                            calculation_entries
                        )
                        if transaction_capital_gain > 0:
                            capital_gain += transaction_capital_gain
                        else:
                            capital_loss += transaction_capital_gain
                        if spin_off_entry is not None:
                            spin_off = spin_off_entry.spin_off
                            assert spin_off is not None
                            calculation_log[spin_off.date][
                                f"spin-off${spin_off.source}"
                            ] = [spin_off_entry]

            # Excess Reported incomes should be reported at the end of the day
            if date_index in self.eris:
                for symbol in self.eris[date_index]:
                    maybe_entry = self.process_eri(symbol, date_index)
                    if not maybe_entry:
                        continue

                    if date_index >= tax_year_start_index:
                        eris = maybe_entry.eris
                        assert eris
                        calculation_log[date_index][
                            f"excess-reported-income${symbol}"
                        ] = [maybe_entry]

            # Lastly all the ERI distribution events
            if date_index in self.eris_distribution:
                for symbol in self.eris_distribution[date_index]:
                    data = self.eris_distribution[date_index][symbol]
                    is_interest = symbol in self.interest_fund_tickers
                    if is_interest:
                        self.total_foreign_interest += data.amount
                    self.calculation_log_yields[date_index][
                        f"excess-reported-income-distribution${symbol}"
                    ] = [
                        CalculationEntry(
                            RuleType.EXCESS_REPORTED_INCOME_DISTRIBUTION,
                            quantity=data.quantity,
                            amount=data.amount,
                            new_quantity=data.quantity,
                            gain=None,
                            fees=Decimal(0),
                            new_pool_cost=data.amount,
                            allowable_cost=None,
                            eris=[
                                ExcessReportedIncome(
                                    price=data.price,
                                    symbol=symbol,
                                    date=date_index - ERI_TAX_DATE_DELTA,
                                    distribution_date=date_index,
                                    is_interest=is_interest,
                                ),
                            ],
                        )
                    ]


            sales_tracker = defaultdict(Decimal)
            tax_year = get_tax_year_index_from_date(date_index)

            for broker in self.mixed_funds.keys():
                mixed_fund_log = mixed_funds_log[broker]
                mixed_fund = self.mixed_funds[broker]
                composition = mixed_fund.mixed_fund_composition

                for transaction in [mixed_fund_transaction for mixed_fund_transaction
                                    in mixed_fund.processed_mixed_fund_transaction_log
                                    if mixed_fund_transaction.date == date_index]:
                    if date_index >= tax_year_start_index and len(mixed_fund_log) == 0:
                                mixed_fund_log.append(
                                    MixedFundEntry(
                                        message="Composition at the beginning of the tax year",
                                        movement={},
                                        tax_movement={},
                                        mixed_fund_composition=composition,
                                        remitted_tax_implications=None
                                    )
                                )
                    if transaction.action == ActionType.STOCK_ACTIVITY:
                        if self.tax_filings.get(tax_year) == TaxFilingBasis.REMITTANCE:
                            # If there is an award earning in a remittance basis year, the OWR  part of its earnings is considered as foreign income
                            # It cannot be higher than the post-amount deposited into the account
                            owr_amount = min(transaction.pre_tax_quantity * transaction.price * transaction.owr_rate,
                                             transaction.quantity * transaction.price - transaction.fees)
                            owr, owr_tax = composition.add_money(tax_year, MixedFundMoneyCategory.RELEVANT_FOREIGN_EARNINGS, owr_amount)
                            non_owr, non_owr_tax = composition.add_money(tax_year, MixedFundMoneyCategory.EMPLOYMENT_INCOME, transaction.quantity * transaction.price - owr_amount - transaction.fees)
                            movement = aggregate_dicts(owr, non_owr)
                            tax_movement = aggregate_dicts(owr_tax, non_owr_tax)

                            message = (
                            "[MIXED FUND EVENT] RSU vesting on %s in %s %s units (%s post-tax) in a tax year filed on remittance basis "
                            "leads to £%s deposited in employment income and %s deposited in foreign income (OWR)"
                            ) % (
                            date_index,
                            broker,
                            transaction.pre_tax_quantity,
                            transaction.quantity,
                            round_decimal(transaction.quantity * transaction.price - owr_amount - transaction.fees, 2),
                            round_decimal(owr_amount, 2),
                            )
                            LOGGER.debug(message)
                            if date_index >= tax_year_start_index:
                                mixed_fund_log.append(
                                    MixedFundEntry(
                                        message=message,
                                        movement=movement,
                                        tax_movement=tax_movement,
                                        mixed_fund_composition=composition,
                                        remitted_tax_implications=None
                                    )
                                )
                        else:
                            # In arising basis tax years, all the RSU amount is considered taxed
                            movement, tax_movement = composition.add_money(tax_year, MixedFundMoneyCategory.EMPLOYMENT_INCOME, transaction.quantity * transaction.price - transaction.fees)

                            message = (
                            "[MIXED FUND EVENT] RSU vesting on %s in %s %s units (%s post-tax) in a tax year filed on arising basis "
                            "leads to £%s deposited in employment income"
                            ) % (
                            date_index,
                            broker,
                            transaction.pre_tax_quantity,
                            transaction.quantity,
                            round_decimal(transaction.quantity * transaction.price - transaction.fees, 2),
                            )
                            LOGGER.debug(message)
                            if date_index >= tax_year_start_index:
                                mixed_fund_log.append(
                                    MixedFundEntry(
                                        message=message,
                                        movement=movement,
                                        tax_movement=tax_movement,
                                        mixed_fund_composition=composition,
                                        remitted_tax_implications=None
                                    )
                                )
                    elif transaction.action == ActionType.WIRE_FUNDS_RECEIVED:
                        if transaction.origin == Origin.NON_UK_TAXED:
                            # If this is a non-UK-taxed transfer-in, add in the foreign income
                            movement, tax_movement = composition.add_money(tax_year, MixedFundMoneyCategory.RELEVANT_FOREIGN_INCOME, transaction.amount - transaction.fees)
                            message = (
                            "[MIXED FUND EVENT] Transfer-in on %s in %s of non-UK taxed money leads to £%s "
                            "deposited in foreign income"
                            ) % (
                            date_index,
                            broker,
                            round_decimal(transaction.amount - transaction.fees, 2),
                            )
                            LOGGER.debug(message)
                            if date_index >= tax_year_start_index:
                                mixed_fund_log.append(
                                    MixedFundEntry(
                                        message=message,
                                        movement=movement,
                                        tax_movement=tax_movement,
                                        mixed_fund_composition=composition,
                                        remitted_tax_implications=None
                                    )
                                )
                        else:
                            # If this is a UK-taxed transfer-in, add in employment income
                            # Positive fees & adjustments will also go there
                            movement, tax_movement = composition.add_money(tax_year, MixedFundMoneyCategory.EMPLOYMENT_INCOME, transaction.amount - transaction.fees)
                            message = (
                            "[MIXED FUND EVENT] Transfer-in on %s in %s of UK taxed money leads to £%s deposited "
                            "in employment income"
                            ) % (
                            date_index,
                            broker,
                            round_decimal(transaction.amount - transaction.fees, 2),
                            )
                            LOGGER.debug(message)
                            if date_index >= tax_year_start_index:
                                mixed_fund_log.append(
                                    MixedFundEntry(
                                        message=message,
                                        movement=movement,
                                        tax_movement=tax_movement,
                                        mixed_fund_composition=composition,
                                        remitted_tax_implications=None
                                    )
                                )
                    elif transaction.action == ActionType.TRANSFER:
                        # Transfers have negative amount
                        withdrawal = -transaction.amount - transaction.fees
                        if transaction.destination == Destination.OVERSEAS:
                            # If this is a transfer out to overseas, then we take the money prorated on all buckets, as per RDRM35420
                            movement, tax_movement = composition.withdraw_money_prorated(withdrawal)
                            message = (
                            "[MIXED FUND EVENT] Transfer-out on %s in %s to overseas destination leads to £%s "
                            "removed prorated on all buckets"
                            ) % (
                            date_index,
                            broker,
                            round_decimal(withdrawal, 2),
                            )
                            LOGGER.debug(message)
                            if date_index >= tax_year_start_index:
                                mixed_fund_log.append(
                                    MixedFundEntry(
                                        message=message,
                                        movement=movement,
                                        tax_movement=tax_movement,
                                        mixed_fund_composition=composition,
                                        remitted_tax_implications=None
                                    )
                                )
                        else:
                            # If this is a transfer out to the UK (=remittance), then the ordering rules apply as per RDRM35240
                            movement, tax_movement = composition.withdraw_money_buckets_order(withdrawal)

                            message = (
                            "[MIXED FUND EVENT] Transfer-out on %s in %s to the UK: remittance leads to £%s removed following the ordering rules"
                            ) % (
                            date_index,
                            broker,
                            round_decimal(withdrawal, 2),
                            )
                            LOGGER.debug(message)

                            remitted_tax_implications = dict()
                            for tax_year in movement.keys():
                                # There is possibly a tax implication only when we remit money from a year that was taxed as remittance
                                if self.tax_filings.get(tax_year) == TaxFilingBasis.REMITTANCE:
                                    for category, remittance in movement[tax_year].items():
                                        if remittance:
                                            if category in [
                                                MixedFundMoneyCategory.RELEVANT_FOREIGN_EARNINGS,
                                                MixedFundMoneyCategory.FOREIGN_SPECIFIC_EMPLOYMENT_INCOME,
                                                MixedFundMoneyCategory.RELEVANT_FOREIGN_INCOME,
                                                MixedFundMoneyCategory.OTHER_INCOME,
                                                ]:
                                                remitted_tax_implications[RemittedIncomeType.INCOME] = (-remittance, 0)
                                            elif category ==  MixedFundMoneyCategory.FOREIGN_CHARGEABLE_GAINS:
                                                remitted_tax_implications[RemittedIncomeType.CAPITAL_GAIN] = (-remittance, 0)
                                            elif category in [
                                                MixedFundMoneyCategory.EMPLOYMENT_INCOME_SUBJECT_TO_A_FOREIGN_FAX,
                                                MixedFundMoneyCategory.RELEVANT_FOREIGN_INCOME_SUBJECT_TO_A_FOREIGN_FAX,
                                            ]:
                                                foreign_tax = tax_movement[tax_year][category]
                                                remitted_tax_implications[RemittedIncomeType.INCOME] = (-remittance, -foreign_tax)
                                            elif category == MixedFundMoneyCategory.FOREIGN_CHARGEABLE_GAINS_SUBJECT_TO_A_FOREIGN_FAX:
                                                foreign_tax = tax_movement[tax_year][category]
                                                remitted_tax_implications[RemittedIncomeType.CAPITAL_GAIN] = (-remittance, -foreign_tax)


                            if date_index >= tax_year_start_index:
                                mixed_fund_log.append(
                                    MixedFundEntry(
                                        message=message,
                                        movement=movement,
                                        tax_movement=tax_movement,
                                        mixed_fund_composition=composition,
                                        remitted_tax_implications=remitted_tax_implications
                                    )
                                )
                    elif transaction.action == ActionType.INTEREST:
                        if transaction.tax_at_source:
                            # Investment gains subject to a foreign tax go to a specific bucket
                            amount = transaction.amount - transaction.fees
                            tax_amount = -transaction.tax_at_source

                            movement, tax_movement = composition.add_money(tax_year, MixedFundMoneyCategory.FOREIGN_CHARGEABLE_GAINS_SUBJECT_TO_A_FOREIGN_FAX, amount, tax_amount)

                            message = (
                            "[MIXED FUND EVENT] Interest on %s in %s accrued leads to £%s deposited in foreign gains " 
                            "subject to foreign tax with foreign tax (foreign tax: £%s) "
                            ) % (
                            date_index,
                            broker,
                            round_decimal(amount, 2),
                            round_decimal(tax_amount, 2),
                            )
                            LOGGER.debug(message)
                            if date_index >= tax_year_start_index:
                                mixed_fund_log.append(
                                    MixedFundEntry(
                                        message=message,
                                        movement=movement,
                                        tax_movement=tax_movement,
                                        mixed_fund_composition=composition,
                                        remitted_tax_implications=None
                                    )
                                )
                        else:
                            # Investment gains not subject to a foreign tax have a specific bucket
                            movement, tax_movement = composition.add_money(tax_year, MixedFundMoneyCategory.FOREIGN_CHARGEABLE_GAINS, transaction.amount - transaction.fees)

                            message = (
                            "[MIXED FUND EVENT] Interest on %s in %s accrued "
                            "without foreign tax leads to £%s deposited in foreign gains"
                            ) % (
                            date_index,
                            broker,
                            round_decimal(transaction.amount - transaction.fees, 2),
                            )
                            LOGGER.debug(message)
                            if date_index >= tax_year_start_index:
                                mixed_fund_log.append(
                                    MixedFundEntry(
                                        message=message,
                                        movement=movement,
                                        tax_movement=tax_movement,
                                        mixed_fund_composition=composition,
                                        remitted_tax_implications=None
                                    )
                                )

                    elif transaction.action == ActionType.DIVIDEND:
                        if transaction.tax_at_source:
                            # Investment gains subject to a foreign tax go to a specific bucket
                            amount = transaction.amount - transaction.fees
                            tax_amount = -transaction.tax_at_source

                            movement, tax_movement = composition.add_money(tax_year, MixedFundMoneyCategory.FOREIGN_CHARGEABLE_GAINS_SUBJECT_TO_A_FOREIGN_FAX, amount, tax_amount)

                            message = (
                            "[MIXED FUND EVENT] %s Dividend on %s in %s accrued leads to £%s deposited in foreign " 
                            " gains subject to foreign tax (foreign tax: £%s) "
                            ) % (
                            transaction.symbol,
                            date_index,
                            broker,
                            round_decimal(amount, 2),
                            round_decimal(tax_amount, 2),
                            )
                            LOGGER.debug(message)
                            if date_index >= tax_year_start_index:
                                mixed_fund_log.append(
                                    MixedFundEntry(
                                        message=message,
                                        movement=movement,
                                        tax_movement=tax_movement,
                                        mixed_fund_composition=composition,
                                        remitted_tax_implications=None
                                    )
                                )
                        else:
                            # Investment gains not subject to a foreign tax have a specific bucket
                            movement, tax_movement = composition.add_money(tax_year, MixedFundMoneyCategory.FOREIGN_CHARGEABLE_GAINS, transaction.amount - transaction.fees)

                            message = (
                            "[MIXED FUND EVENT] %s Dividend on %s in %s accrued "
                            "without foreign tax leads to £%s deposited in foreign gains"
                            ) % (
                            transaction.symbol,
                            date_index,
                            broker,
                            round_decimal(transaction.amount - transaction.fees, 2),
                            )
                            LOGGER.debug(message)
                            if date_index >= tax_year_start_index:
                                mixed_fund_log.append(
                                    MixedFundEntry(
                                        message=message,
                                        movement=movement,
                                        tax_movement=tax_movement,
                                        mixed_fund_composition=composition,
                                        remitted_tax_implications=None
                                    )
                                )

                    elif transaction.action in [ActionType.FEE, ActionType.ADJUSTMENT]:
                        if transaction.amount > 0:
                            # Adjustments are pure capital
                            movement, tax_movement = composition.add_money(tax_year, MixedFundMoneyCategory.OTHER_INCOME, transaction.amount - transaction.fees)

                            message = (
                            "[MIXED FUND EVENT] Adjustments accrued on %s in %s leads to £%s deposited "
                            "in pure capital"
                            ) % (
                            date_index,
                            broker,
                            round_decimal(transaction.amount - transaction.fees, 2),
                            )
                            LOGGER.debug(message)
                            if date_index >= tax_year_start_index:
                                mixed_fund_log.append(
                                    MixedFundEntry(
                                        message=message,
                                        movement=movement,
                                        tax_movement=tax_movement,
                                        mixed_fund_composition=composition,
                                        remitted_tax_implications=None
                                    )
                                )
                        else:
                            # Negative fees or adjustments are considered overseas transfers
                            withdrawal = -transaction.amount - transaction.fees
                            movement, tax_movement = composition.withdraw_money_prorated(withdrawal)
                            message = (
                            "[MIXED FUND EVENT] Fee/adjustment on %s in %s treated as overseas transfer leads to "
                            "£%s removed prorated on all buckets"
                            ) % (
                            date_index,
                            broker,
                            round_decimal(-transaction.amount - transaction.fees, 2),
                            )
                            LOGGER.debug(message)
                            if date_index >= tax_year_start_index:
                                mixed_fund_log.append(
                                    MixedFundEntry(
                                        message=message,
                                        movement=movement,
                                        tax_movement=tax_movement,
                                        mixed_fund_composition=composition,
                                        remitted_tax_implications=None
                                    )
                                )

                    elif transaction.action == ActionType.SELL:
                        # For sales, we need to match to the right CGT events to find the cost basis
                        # First, get all cost bases for the disposals of this symbol on that date
                        matchable_sales = all_sales_log[date_index][f"sell${transaction.symbol}"]
                        cost_bases = []

                        for rule in [RuleType.SAME_DAY, RuleType.BED_AND_BREAKFAST, RuleType.SECTION_104]:
                            for entry in [entry for entry in matchable_sales if entry.rule_type == rule]:
                                cost_basis = entry.allowable_cost / entry.quantity
                                cost_bases.append(
                                    [entry.quantity, rule, cost_basis]
                                )

                        # Iterate over them to find enough events to cover the sold quantity. Skip events corresponding
                        # to quantities already sold for the same symbol on the same day on other brokers
                        sales = []
                        skip_remaining = sales_tracker[transaction.symbol]
                        take_remaining = transaction.quantity

                        for quantity, rule, cost_basis in cost_bases:
                            if take_remaining <= 0:
                                break

                            # Skip already-used
                            if skip_remaining >= quantity:
                                skip_remaining -= quantity
                                continue
                            elif skip_remaining > 0:
                                quantity -= skip_remaining
                                skip_remaining = Decimal(0)

                            # Take quantity
                            taken = min(quantity, take_remaining)

                            sales.append((taken, rule, cost_basis))

                            take_remaining -= taken

                        if take_remaining > 0:
                            raise ValueError("Not enough calculation entries to satisfy sale amount")


                        for quantity, rule, cost_basis in sales:

                            chargeable_gain = (transaction.price - cost_basis) * quantity - transaction.fees * quantity  / transaction.quantity
                            if chargeable_gain > 0:
                                movement, tax_movement = composition.add_money(tax_year, MixedFundMoneyCategory.FOREIGN_CHARGEABLE_GAINS, chargeable_gain)

                                message = (
                                "[MIXED FUND EVENT] %s sale on %s in %s of %s units via %s "
                                 "leads to £%s capital gain"
                                ) % (
                                 transaction.symbol,
                                date_index,
                                broker,
                                quantity,
                                rule.name,
                                round_decimal(chargeable_gain, 2),
                                )
                                LOGGER.debug(message)
                                if date_index >= tax_year_start_index:
                                    mixed_fund_log.append(
                                    MixedFundEntry(
                                        message=message,
                                        movement=movement,
                                        tax_movement=tax_movement,
                                        mixed_fund_composition=composition,
                                        remitted_tax_implications=None
                                    )
                                )
                    else:
                        raise f"ERROR: a mixed fund transaction is of an unsupported type: {transaction.action}"



        self.process_dividends()
        self.process_interests()

        print("Second pass completed")
        allowance = CAPITAL_GAIN_ALLOWANCES.get(self.tax_year)
        dividend_allowance = DIVIDEND_ALLOWANCES.get(self.tax_year)

        return CapitalGainsReport(
            self.tax_year,
            [
                self.make_portfolio_entry(symbol, position.quantity, position.amount)
                for symbol, position in self.portfolio.items()
            ],
            disposal_count,
            disposed_symbols,
            round_decimal(disposal_proceeds, 2),
            round_decimal(allowable_costs, 2),
            round_decimal(capital_gain, 2),
            round_decimal(capital_loss, 2),
            Decimal(allowance) if allowance is not None else None,
            Decimal(dividend_allowance) if dividend_allowance is not None else None,
            calculation_log,
            dict(sorted(self.calculation_log_yields.items())),
            round_decimal(self.total_uk_interest, 2),
            round_decimal(self.total_foreign_interest, 2),
            show_unrealized_gains=self.calc_unrealized_gains,
            mixed_funds_log=mixed_funds_log
        )

    def calculate_mixed_fund_states(self) -> MixedFundsReport:
        """Calculates the state of the mixed fund's balances in each bucket transaction by transaction.
        Returns a report of the current tax's year mixed fund movements tax movements & implications"""


    def make_portfolio_entry(
        self, symbol: str, quantity: Decimal, amount: Decimal
    ) -> PortfolioEntry:
        """Create a portfolio entry in the report."""
        # (by calculating the unrealized gains)
        unrealized_gains = None
        if self.calc_unrealized_gains:
            current_price = (
                self.price_fetcher.get_current_market_price(symbol)
                if quantity > 0
                else 0
            )
            if current_price is not None:
                unrealized_gains = current_price * quantity - amount
        return PortfolioEntry(
            symbol,
            quantity,
            amount,
            unrealized_gains,
        )


def calculate_cgt(args: argparse.Namespace) -> None:
    """Perform all the computations."""

    # Read data from input files
    broker_transactions = read_broker_transactions(
        freetrade_transactions_file=args.freetrade_file,
        schwab_transactions_file=args.schwab_file,
        schwab_awards_transactions_file=args.schwab_award_file,
        schwab_equity_award_json_transactions_file=args.schwab_equity_award_json,
        schwab_transfers_file=args.schwab_transfer_file,
        trading212_transactions_folder=args.trading212_dir,
        mssb_transactions_folder=args.mssb_dir,
        sharesight_transactions_folder=args.sharesight_dir,
        raw_transactions_file=args.raw_file,
        vanguard_transactions_file=args.vanguard_file,
        eri_raw_file=args.eri_raw_file,
    )
    currency_converter = CurrencyConverter(args.exchange_rates_file)
    price_fetcher = CurrentPriceFetcher(currency_converter)
    initial_prices = InitialPrices(args.initial_prices_file)
    spin_off_handler = SpinOffHandler(args.spin_offs_file)
    isin_converter = IsinConverter(args.isin_translation_file)
    tax_filings = read_remittance_basis(args.remittance_basis_file)
    owr_events = read_owr(args.owr_file)

    calculator = CapitalGainsCalculator(
        args.year,
        currency_converter,
        isin_converter,
        price_fetcher,
        spin_off_handler,
        initial_prices,
        args.interest_fund_tickers,
        tax_filings,
        owr_events,
        balance_check=args.balance_check,
        calc_unrealized_gains=args.calc_unrealized_gains,

    )
    # First pass converts broker transactions to HMRC transactions.
    # This means applying same day rule and collapsing all transactions with
    # same type within the same day.
    # It also converts prices to GBP, validates data and calculates dividends,
    # taxes on dividends and interest.
    calculator.convert_to_hmrc_transactions(broker_transactions)

    # Mixed funds events pre-processing grabs MixedFund events that have been organized during the first pass and
    # transforms them to be ready for mixed fund calculation later
    calculator.preprocess_mixed_funds()
    # Second pass calculates capital gain tax for the given tax year.
    report = calculator.calculate_capital_gain()
    print(report)

    # Generate PDF report.
    if not args.no_report:
        render_latex.render_pdf(
            report,
            output_path=args.output,
            skip_pdflatex=args.no_pdflatex,
            is_mixed_fund=False
        )

        if report.mixed_funds_log:
            render_latex.render_pdf(
            report,
            output_path=args.output_mixed_fund,
            skip_pdflatex=args.no_pdflatex,
            is_mixed_fund=True
        )
    print("All done!")


def main() -> int:
    """Run main function."""

    # Enable colourised logging.
    setup_logging()

    # Throw exception on accidental float usage
    decimal.getcontext().traps[decimal.FloatOperation] = True

    parser = create_parser()

    if len(sys.argv) == 1:
        parser.print_help()
        return 0

    args = parser.parse_args()

    logging_level = logging.DEBUG if args.verbose else logging.WARNING
    logging.getLogger().setLevel(logging_level)

    try:
        calculate_cgt(args)
    except CgtError as err:
        if args.verbose:
            LOGGER.exception("Exception:")
        else:
            # Print error without traceback
            LOGGER.error("%s", err)
        return 1
    except Exception:
        # Last-resort catch for unexpected exceptions
        LOGGER.critical("Unexpected error!")
        LOGGER.exception("Details:")

    return 0


def init() -> None:
    """Entry point."""
    sys.exit(main())


if __name__ == "__main__":
    init()
