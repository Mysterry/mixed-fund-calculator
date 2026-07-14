"""Model classes."""

from __future__ import annotations

from dataclasses import dataclass, field
import datetime
from datetime import timedelta
from decimal import Decimal, ROUND_DOWN, ROUND_HALF_UP
from enum import Enum
from typing import TYPE_CHECKING, DefaultDict, Final
from collections import defaultdict

from .exceptions import InvalidTransactionError
from .util import approx_equal, round_decimal

if TYPE_CHECKING:
    from collections.abc import Generator


@dataclass
class SpinOff:
    """Class representing spin-off event on a share."""

    # Cost proportion to be applied to the cost of original shares from which
    # Spin-off originated
    cost_proportion: Decimal
    # Source of the Spin-off, e.g MMM for SOLV
    source: str
    # Dest ticker to which SpinOff happened, e.g. SOLV for MMM
    dest: str
    # When the spin-off happened
    date: datetime.date


@dataclass
class TaxTreaty:
    """Class representing a treaty between UK and different countries.

    treaty_rate is the dividend rate creditable against UK tax under the
    treaty. The credit is only claimed when at least that much foreign tax
    was actually withheld.
    """

    country: str
    treaty_rate: Decimal


class RemittedIncomeType(Enum):
    INCOME = 0
    CAPITAL_GAIN = 1


class Destination(str, Enum):
    OVERSEAS = "Overseas"
    UK = "UK"


@dataclass
class ExcessReportedIncome:
    """Class representing Excess Reported Income on a fund.

    The income is reported on a fund at the end of its reporting period.
    The income represent an increase of the cost basis at that date and a
    taxable event at the distribution date.
    """

    price: Decimal
    symbol: str
    date: datetime.date
    distribution_date: datetime.date
    is_interest: bool


@dataclass
class ExcessReportedIncomeDistribution:
    """Class representing Excess Reported Income distribution event on a fund.

    This is when the income is distributed to you for tax purposes.
    """

    price: Decimal = Decimal(0)
    amount: Decimal = Decimal(0)
    quantity: Decimal = Decimal(0)

    def __add__(
        self, transaction: ExcessReportedIncomeDistribution
    ) -> ExcessReportedIncomeDistribution:
        """Add two tax transactions."""
        return self.__class__(
            price=transaction.price,
            amount=self.amount + transaction.amount,
            quantity=self.quantity + transaction.quantity,
        )


@dataclass
class HmrcTransactionData:
    """Hmrc transaction figures."""

    quantity: Decimal = Decimal(0)
    amount: Decimal = Decimal(0)
    fees: Decimal = Decimal(0)
    # This is a list to support Bed and Breakfast acquisitions that can cross multiple
    # ERI reports for the same fund. This can happen for example when a fund is
    # liquidated close after its usual reporting data, requiring a new final reporting.
    eris: list[ExcessReportedIncome] = field(default_factory=list)

    def __add__(self, transaction: HmrcTransactionData) -> HmrcTransactionData:
        """Add two transactions."""
        return self.__class__(
            self.quantity + transaction.quantity,
            self.amount + transaction.amount,
            self.fees + transaction.fees,
            self.eris + transaction.eris,
        )


@dataclass
class ForeignCurrencyAmount:
    """Represent a decimal amount in foreign currency."""

    amount: Decimal = Decimal(0)
    currency: str = ""

    def __add__(self, amount: ForeignCurrencyAmount) -> ForeignCurrencyAmount:
        """Add two amounts."""
        assert self.currency or not self.amount, (
            f"Invalid foreign currency amount {self}"
        )
        assert amount.currency or not amount.amount, (
            f"Invalid foreign currency amount {amount}"
        )
        assert (
            not self.currency or not amount.currency or self.currency == amount.currency
        ), f"Incompatible currency operation {self.currency} vs {amount.currency}"
        result = ForeignCurrencyAmount(
            amount=self.amount + amount.amount,
            currency=self.currency or amount.currency,
        )
        assert result.currency or not result.amount, (
            f"Invalid foreign currency result {result}"
        )
        return result


HmrcTransactionLog = dict[datetime.date, dict[str, HmrcTransactionData]]
ForeignAmountLog = dict[tuple[str, datetime.date], ForeignCurrencyAmount]
ExcessReportedIncomeLog = dict[datetime.date, dict[str, ExcessReportedIncome]]
ExcessReportedIncomeDistributionLog = dict[
    datetime.date, dict[str, ExcessReportedIncomeDistribution]
]

class ActionType(Enum):
    """Type of transaction action."""

    BUY = 1
    SELL = 2
    TRANSFER = 3
    STOCK_ACTIVITY = 4
    DIVIDEND = 5
    DIVIDEND_TAX = 6
    FEE = 7
    ADJUSTMENT = 8
    CAPITAL_GAIN = 9
    SPIN_OFF = 10
    INTEREST = 11
    REINVEST_SHARES = 12
    REINVEST_DIVIDENDS = 13
    WIRE_FUNDS_RECEIVED = 14
    STOCK_SPLIT = 15
    STOCK_REVERSE_SPLIT = 16
    CASH_MERGER = 17
    EXCESS_REPORTED_INCOME = 18
    FULL_REDEMPTION = 19
    EXPIRATION = 20
    BUY_OPTION = 21
    SELL_OPTION = 22
    NRA_TAX_ADJ = 23
    BOOKKEEPING = 24


class CalculationType(Enum):
    """Calculation type enumeration."""

    ACQUISITION = 1
    DISPOSAL = 2


@dataclass
class BrokerTransaction:
    """Broken transaction data."""

    date: datetime.date
    action: ActionType
    symbol: str | None
    description: str
    quantity: Decimal | None
    price: Decimal | None
    fees: Decimal
    amount: Decimal | None
    currency: str
    broker: str
    isin: str | None = None
    destination: str | None = None
    origin: str | None = None
    pre_tax_quantity: Decimal | None = None

    def find_close_event(self, event_list: list, min_delta=1, max_delta=1):
        """Given a transaction, looks in a list of objects with data attribute for one whose date is comprised between this
        transaction's date - min_delta and date + max_delta. Raises an error if more than 1 object is found, returns None if 0"""
        filtered_event_list = [event for event in event_list if
                                     self.date - timedelta(days=min_delta) <= event.date <= self.date + timedelta(days=max_delta)]
        if len(filtered_event_list) == 0:
            return None
        elif len(filtered_event_list) > 1:
            raise InvalidTransactionError(self, message="More than 1 close event found")
        elif len(filtered_event_list) == 1:
            return filtered_event_list[0]



class RuleType(Enum):
    """HMRC rule type."""

    SECTION_104 = 1
    SAME_DAY = 2
    BED_AND_BREAKFAST = 3
    SPIN_OFF = 4
    DIVIDEND = 5
    INTEREST = 6
    EXCESS_REPORTED_INCOME = 7
    EXCESS_REPORTED_INCOME_DISTRIBUTION = 8


@dataclass
class ProcessedMixedFundTransaction:
    broker: str
    date: datetime.date
    action: ActionType
    amount: Decimal | None = None
    quantity: Decimal | None = None
    fees: Decimal | None = Decimal(0)
    price: Decimal | None = None
    symbol: str | None = None
    origin: str | None = None
    destination: str | None = None
    owr_rate: Decimal | None = None
    tax_at_source: Decimal | None = None
    pre_tax_quantity: Decimal | None = None


class MixedFundMoneyCategory(Enum):
    """"Class representing the different categories of money in a mixed fund.
    These are officially defined in RDRM35240"""

    EMPLOYMENT_INCOME = 1
    RELEVANT_FOREIGN_EARNINGS = 2
    FOREIGN_SPECIFIC_EMPLOYMENT_INCOME = 3
    RELEVANT_FOREIGN_INCOME = 4
    FOREIGN_CHARGEABLE_GAINS = 5
    EMPLOYMENT_INCOME_SUBJECT_TO_A_FOREIGN_FAX = 6
    RELEVANT_FOREIGN_INCOME_SUBJECT_TO_A_FOREIGN_FAX = 7
    FOREIGN_CHARGEABLE_GAINS_SUBJECT_TO_A_FOREIGN_FAX = 8
    OTHER_INCOME = 9
    TRF_CAPITAL = 10


# Categories that are already fully taxed as ordinary UK income when they arise,
# regardless of the tax filing basis of the year. Remitting money from these
# categories creates no further UK tax implication due to remittance, and they
# cannot be designated as TRF Capital (there is nothing left for TRF to relieve).
ALREADY_UK_TAXED_CATEGORIES: Final[frozenset[MixedFundMoneyCategory]] = frozenset(
    {
        MixedFundMoneyCategory.EMPLOYMENT_INCOME,
        MixedFundMoneyCategory.EMPLOYMENT_INCOME_SUBJECT_TO_A_FOREIGN_FAX,
        MixedFundMoneyCategory.OTHER_INCOME,
    }
)

# RDRM70000: the Temporary Repatriation Facility is available for tax years
# starting 2025, 2026 and 2027.
TRF_RELEVANT_TAX_YEARS: Final[tuple[int, ...]] = (2025, 2026, 2027)

# Sentinel "tax_year" bucket key for TRF Capital: TRF Capital has no
# associated tax year. Using a value larger than any real tax year means
# get_next_none_empty_bucket()'s `sorted(..., reverse=True)` naturally checks
# this bucket FIRST, giving TRF Capital remittance priority over every other
# bucket with zero extra code in get_next_none_empty_bucket/
# withdraw_money_buckets_order. It also sorts first (leftmost) in the
# "by tax year and type" tables, which is consistent with it being the
# highest-priority money.
TRF_CAPITAL_TAX_YEAR: Final[int] = 999999


class Period(Enum):
    """4-way grouping of mixed-fund money for TRF/remittance breakdowns."""

    POST_2025 = "post_2025"
    PRE_2025_REMITTANCE = "pre_2025_remittance"
    PRE_2025_ARISING = "pre_2025_arising"
    TRF_CAPITAL = "trf_capital"


_PERIOD_ORDER: Final[dict[Period, int]] = {
    Period.POST_2025: 0,
    Period.PRE_2025_REMITTANCE: 1,
    Period.PRE_2025_ARISING: 2,
    Period.TRF_CAPITAL: 3,
}


def get_period(tax_year: int, tax_filings=None) -> Period:
    """Classify a bucket's tax_year.

    Pre-2025 years are split by filing basis: remittance basis years are TRF-eligible,
    arising basis years are already UK-taxed so TRF buys nothing on them.
    """
    if tax_year == TRF_CAPITAL_TAX_YEAR:
        return Period.TRF_CAPITAL
    if tax_year >= 2025:
        return Period.POST_2025
    if tax_filings is not None:
        basis = tax_filings.get(tax_year)
        if basis is not None and basis.value:  # TaxFilingBasis.REMITTANCE.value == 1
            return Period.PRE_2025_REMITTANCE
    return Period.PRE_2025_ARISING


_CENT: Final = Decimal("0.01")


class MixedFundComposition:
    """Class representing a mixed's fund composition. This is the representation of the mixed's fund according to
    HMRC's mixed funds rules: it represents at all time the GBP cost of the book.
    The composition is maintained at tax_year x category, following the specs of RDRM35240"""
    broker: str
    buckets: DefaultDict[int, DefaultDict[MixedFundMoneyCategory, Decimal]]
    tax_buckets: DefaultDict[int, DefaultDict[MixedFundMoneyCategory, Decimal]]

    def __init__(
            self,
            broker: str
        ):
            """Create empty mixed fund composition"""
            self.broker = broker
            self.buckets = defaultdict(lambda: defaultdict(Decimal))
            self.tax_buckets = defaultdict(lambda: defaultdict(Decimal))

    def get_next_none_empty_bucket(self) -> tuple[int, MixedFundMoneyCategory] | None:
        """Returns as a list [tax_year, mixed_fund_money_category] the last bucket with non-zero amount"""

        for tax_year in sorted(self.buckets.keys(), reverse=True):
            for category in MixedFundMoneyCategory:
                amount = self.buckets[tax_year][category]
                if amount:
                    return tax_year, category
        return None

    def add_money(self, tax_year: int, category: MixedFundMoneyCategory, amount: Decimal, tax_amount=None) \
        -> tuple[dict[int, dict[MixedFundMoneyCategory, Decimal]], dict[int, dict[MixedFundMoneyCategory, Decimal]]]:
        """Money is added in the relevant category bucket, rounded to the nearest cent."""

        amount = Decimal(amount).quantize(_CENT, rounding=ROUND_HALF_UP)
        if amount < 0:
            raise ValueError("Cannot add negative amount to a mixed fund")
        if tax_amount is not None:
            tax_amount = Decimal(tax_amount).quantize(_CENT, rounding=ROUND_HALF_UP)
        if tax_amount and tax_amount < 0:
            raise ValueError("Cannot add negative tax amount to a mixed fund")
        self.buckets[tax_year][category] += amount
        if tax_amount:
            if category in [
                MixedFundMoneyCategory.EMPLOYMENT_INCOME_SUBJECT_TO_A_FOREIGN_FAX,
                MixedFundMoneyCategory.RELEVANT_FOREIGN_INCOME_SUBJECT_TO_A_FOREIGN_FAX,
                MixedFundMoneyCategory.FOREIGN_CHARGEABLE_GAINS_SUBJECT_TO_A_FOREIGN_FAX,
                MixedFundMoneyCategory.TRF_CAPITAL,
            ]:
                self.tax_buckets[tax_year][category] += tax_amount
            else:
                raise ValueError("Cannot add tax amount to a category not subject to foreign tax")
        return dict({tax_year: dict({category: amount})}), dict({tax_year: dict({category: tax_amount})})

    def remove_money(self, tax_year: int, category: MixedFundMoneyCategory, amount: Decimal, tax_amount=None) \
        -> tuple[dict[int, dict[MixedFundMoneyCategory, Decimal]], dict[int, dict[MixedFundMoneyCategory, Decimal]]]:
        """Money is removed from the relevant category bucket. Inverse of add_money."""

        amount = Decimal(amount).quantize(_CENT, rounding=ROUND_DOWN)
        if tax_amount is not None:
            tax_amount = Decimal(tax_amount).quantize(_CENT, rounding=ROUND_DOWN)
        if amount < 0:
            raise ValueError("Cannot remove negative amount from a mixed fund")
        if tax_amount and tax_amount < 0:
            raise ValueError("Cannot remove negative tax amount from a mixed fund")
        available = self.buckets[tax_year][category]
        if amount > available:
            raise ValueError(
                f"Cannot remove £{amount} from ({tax_year}, {category}) in {self.broker}: "
                f"only £{available} available"
            )
        self.buckets[tax_year][category] -= amount
        if tax_amount:
            tax_available = self.tax_buckets[tax_year][category]
            if tax_amount > tax_available:
                raise ValueError(
                    f"Cannot remove £{tax_amount} foreign tax from ({tax_year}, {category}) "
                    f"in {self.broker}: only £{tax_available} available"
                )
            self.tax_buckets[tax_year][category] -= tax_amount
        return (
            dict({tax_year: dict({category: -amount})}),
            dict({tax_year: dict({category: -tax_amount if tax_amount else Decimal(0)})}),
        )


    def purge(self) -> tuple[dict[int, dict[MixedFundMoneyCategory, Decimal]], dict[int, dict[MixedFundMoneyCategory, Decimal]]]:
        """Reset every bucket to zero.

        Used when the account's real value has gone to zero (fully closed): any
        composition still on the books at that point must be drift -- e.g. from
        capital losses, which reduce the account's real value but are never
        recognised as reducing the mixed fund (RDRM/CGM have no rule for this; see
        main.py's account-closure check) -- rather than genuine remaining value.
        Returns the removed amounts as a negative movement, for logging.
        """
        movement: dict[int, dict[MixedFundMoneyCategory, Decimal]] = {}
        tax_movement: dict[int, dict[MixedFundMoneyCategory, Decimal]] = {}
        for tax_year, categories in self.buckets.items():
            for category, amount in categories.items():
                if amount:
                    movement.setdefault(tax_year, {})[category] = -amount
                tax_amount = self.tax_buckets[tax_year][category]
                if tax_amount:
                    tax_movement.setdefault(tax_year, {})[category] = -tax_amount
        self.buckets = defaultdict(lambda: defaultdict(Decimal))
        self.tax_buckets = defaultdict(lambda: defaultdict(Decimal))
        return movement, tax_movement

    def get_total_amount(self) -> Decimal:
        """Returns total amount in the mixed fund across all tax years and categories."""

        return sum(
            amount
            for year_bucket in self.buckets.values()
            for amount in year_bucket.values()
        )

    def withdraw_money_prorated(self, withdrawal: Decimal) -> tuple[dict[int, dict[MixedFundMoneyCategory, Decimal]], dict[int, dict[MixedFundMoneyCategory, Decimal]]]:
        """Money is removed prorated across all buckets for overseas transfers.

        Each bucket's share is rounded DOWN to the cent; remainder pennies are
        assigned one at a time to the buckets with the smallest balance so that
        smaller buckets are extinguished first.
        """
        withdrawal = Decimal(withdrawal).quantize(_CENT, rounding=ROUND_HALF_UP)
        total = self.get_total_amount()
        withdrawals: defaultdict = defaultdict(lambda: defaultdict(Decimal))
        tax_withdrawals: defaultdict = defaultdict(lambda: defaultdict(Decimal))

        if total < withdrawal:
            raise ValueError("Cannot withdraw amount from mixed fund higher than total value")
        if withdrawal < 0:
            raise ValueError("Cannot withdraw negative amount from mixed fund")

        # Collect non-empty buckets and calculate each bucket's prorated share rounded down.
        bucket_keys = [
            (ty, cat)
            for ty in self.buckets
            for cat in MixedFundMoneyCategory
            if self.buckets[ty][cat]
        ]
        shares: dict[tuple[int, MixedFundMoneyCategory], Decimal] = {
            k: (self.buckets[k[0]][k[1]] * withdrawal / total).quantize(_CENT, rounding=ROUND_DOWN)
            for k in bucket_keys
        }

        # Assign remainder pennies to the smallest-balance buckets first.
        remainder = withdrawal - sum(shares.values())
        for k in sorted(bucket_keys, key=lambda k: self.buckets[k[0]][k[1]]):
            if remainder < _CENT:
                break
            if shares[k] + _CENT <= self.buckets[k[0]][k[1]]:
                shares[k] += _CENT
                remainder -= _CENT

        # Apply withdrawals and proportional tax credits.
        for (ty, cat), share in shares.items():
            if not share:
                continue
            amount = self.buckets[ty][cat]
            tax_amount = self.tax_buckets[ty][cat]
            self.buckets[ty][cat] -= share
            withdrawals[ty][cat] = -share
            if tax_amount:
                tax_share = (share * tax_amount / amount).quantize(_CENT, rounding=ROUND_DOWN)
                self.tax_buckets[ty][cat] -= tax_share
                tax_withdrawals[ty][cat] = -tax_share

        return withdrawals, tax_withdrawals

    def withdraw_money_buckets_order(self, withdrawal: Decimal) -> tuple[dict[int, dict[MixedFundMoneyCategory, Decimal]], dict[int, dict[MixedFundMoneyCategory, Decimal]]]:
        """Money is removed following the buckets' order if destination is UK"""

        withdrawal = Decimal(withdrawal).quantize(_CENT, rounding=ROUND_HALF_UP)
        total = self.get_total_amount()
        withdrawals =  defaultdict(lambda: defaultdict(Decimal))
        tax_withdrawals = defaultdict(lambda: defaultdict(Decimal))

        if total < withdrawal:
            raise ValueError("Cannot withdraw amount from mixed fund higher than total value")
        if withdrawal < 0:
           raise ValueError(f"Cannot withdraw negative amount from mixed fund in {self.broker}: {withdrawal}")

        while withdrawal > 0:
            tax_year, category = self.get_next_none_empty_bucket()
            amount = self.buckets[tax_year][category]
            tax_amount = self.tax_buckets[tax_year][category]
            taken = min(amount, withdrawal)
            self.buckets[tax_year][category] -= taken
            withdrawals[tax_year][category] = -taken
            withdrawal -= taken
            if tax_amount:
                tax_taken = (taken * tax_amount / amount).quantize(_CENT, rounding=ROUND_DOWN)
                self.tax_buckets[tax_year][category] -= tax_taken
                tax_withdrawals[tax_year][category] = -tax_taken

        return withdrawals, tax_withdrawals

    def declare_trf(
        self,
        allocations: dict[tuple[int, MixedFundMoneyCategory], Decimal],
    ) -> tuple[dict[int, dict[MixedFundMoneyCategory, Decimal]], dict[int, dict[MixedFundMoneyCategory, Decimal]]]:
        """Designate pre-2025 amounts as TRF Capital (RDRM70000).

        Moves each (source tax_year, category) amount out of its bucket and into
        the TRF_CAPITAL_TAX_YEAR/TRF_CAPITAL bucket via remove_money/add_money.

        Any foreign tax credit on the source money is extinguished, not carried
        forward: the TRF charge is a flat rate on the gross designated amount,
        with no relief available for foreign tax already paid on it (it cannot be
        set against the TRF charge -- designated amounts are treated as net of
        tax), so tracking a foreign tax credit against TRF Capital would be
        misleading.
        """
        movement: dict[int, dict[MixedFundMoneyCategory, Decimal]] = {}
        tax_movement: dict[int, dict[MixedFundMoneyCategory, Decimal]] = {}

        for (tax_year, category), amount in allocations.items():
            if not amount:
                continue
            if tax_year >= 2025 or category == MixedFundMoneyCategory.TRF_CAPITAL:
                raise ValueError(
                    f"Only pre-2025 amounts can be designated as TRF Capital, got ({tax_year}, {category})"
                )

            available = self.buckets[tax_year][category]
            tax_available = self.tax_buckets[tax_year][category]
            tax_amount = tax_available * amount / available if available else Decimal(0)

            removed, removed_tax = self.remove_money(tax_year, category, amount, tax_amount)
            added, _ = self.add_money(TRF_CAPITAL_TAX_YEAR, MixedFundMoneyCategory.TRF_CAPITAL, amount)

            movement = aggregate_dicts(aggregate_dicts(movement, removed), added)
            tax_movement = aggregate_dicts(tax_movement, removed_tax)

        return movement, tax_movement

    def get_list_representation_buckets(self):
        return get_list_representation_buckets(self.buckets)

    def get_list_representation_tax_buckets(self):
        return get_list_representation_buckets(self.tax_buckets)

def get_list_representation_buckets(
    buckets:  dict[int, dict[MixedFundMoneyCategory, Decimal]]
) -> list[tuple[int, MixedFundMoneyCategory, Decimal]] :
    l = []
    for tax_year in sorted(buckets.keys(), reverse=True):
        for category in sorted(buckets[tax_year].keys(), key=lambda c: c.value):
            amount = buckets[tax_year][category]
            if amount:
                l.append((tax_year, category, amount))
    return l


def aggregate_dicts(
    a: dict[int, dict[MixedFundMoneyCategory, Decimal]],
    b: dict[int, dict[MixedFundMoneyCategory, Decimal]],
) -> dict[int, dict[MixedFundMoneyCategory, Decimal]]:

    result = defaultdict(lambda: defaultdict(Decimal))

    for source in (a, b):
        for tax_year, categories in source.items():
            for category, amount in categories.items():
                result[tax_year][category] += amount if amount else Decimal(0)

    return {tax_year: dict(cats) for tax_year, cats in result.items()}

@dataclass
class MixedFund:
    """"Class representing a broker's mixed fund"""

    broker: str
    mixed_fund_transaction_log: list[BrokerTransaction]
    processed_mixed_fund_transaction_log: list[ProcessedMixedFundTransaction]
    mixed_fund_composition: MixedFundComposition

    def __init__(
        self,
        broker: str
    ):
        """Create empty mixed fund"""
        self.broker = broker
        self.mixed_fund_transaction_log = []
        self.processed_mixed_fund_transaction_log = []
        self.mixed_fund_composition = MixedFundComposition(broker)

    def __repr__(self) -> str:
       """Return string representation."""
       return f"""Mixed fun of: {self.broker} 
           Raw transactions: 
           {'\n'.join(map(str, self.mixed_fund_transaction_log))}
           Pre-processed transactions: 
           {'\n'.join(map(str, self.processed_mixed_fund_transaction_log))}
       """

    def add(self, transaction: BrokerTransaction) -> None:
        """Adds a transaction to the log, only if it is from the right broker and from admittable types"""
        if transaction.broker == self.broker and transaction.action  in [
            ActionType.SELL,
            ActionType.TRANSFER,
            ActionType.STOCK_ACTIVITY,
            ActionType.DIVIDEND,
            ActionType.FEE,
            ActionType.ADJUSTMENT,
            ActionType.INTEREST,
            ActionType.WIRE_FUNDS_RECEIVED,
            ActionType.NRA_TAX_ADJ,
        ]:
            self.mixed_fund_transaction_log.append(transaction)


# NEED A DATA STRUCTURE WHICH LOGS FOR EACH BROKER (SAME TIME AS FIRST PASS):
# ALL UNITARY TRANSACTIONS IN THE TEMPORAL ORDER IF THEY HAVE ONE OF THE MixedFundTransactionType
# AMOUNT MUST BE LOGGED IN GBP AT THE TIME OF TRANSACTION
#
# LATER, NECESSARILY AFTER SECOND PASS WE HAVE A PROCESSING OF THIS DATA STRUCTURE WHICH DOES:
# FOR EACH EARNING: MATCH WITH OWR EVENT AND DISTRIBUTE EARNINGS IN UK_TAXED_EARNINGS OR OWR_EARNINGS
# FOR EACH DISPOSAL: FIND THE RIGHT PRICE VIA THE LIST OF HMRC_DISPOSALS, AND DISTRIBUTE GAIN IN FOREIGN_GAIN
# FOR EACH DIVIDEND_TAX: MATCH WITH THE APPROPRIATE DIVIDENT EVENT
# FOR EACH DIVIDENT W TAX: DISTRIBUTE GAIN - TAX IN GAIN_W_FOREIGN_TAX
# FOR EACH INTEREST / DIVIDENT EVENT WITHOUT TAX: DISTRIBUTE GAIN IN GAIN



@dataclass
class Dividend:
    """Class representing a dividend event."""

    date: datetime.date
    symbol: str
    amount: Decimal
    tax_at_source: Decimal
    is_interest: bool
    tax_treaty: TaxTreaty | None
    # Source country of the dividend, set for foreign dividends even when no
    # treaty credit applies ("Unknown" when the ISIN cannot be determined).
    country: str | None = None

    @property
    def tax_treaty_amount(self) -> Decimal:
        """As title."""
        if self.tax_treaty is None:
            return Decimal(0)
        return self.amount * self.tax_treaty.treaty_rate


@dataclass
class DividendCountrySummary:
    """Per-country foreign dividend totals."""

    amount: Decimal = Decimal(0)
    tax_paid: Decimal = Decimal(0)
    treaty_allowance: Decimal = Decimal(0)


@dataclass
class CgtAssetClassTotals:
    """CGT totals for one SA108 asset class."""

    disposal_count: int = 0
    disposal_proceeds: Decimal = Decimal(0)
    allowable_costs: Decimal = Decimal(0)
    capital_gain: Decimal = Decimal(0)
    capital_loss: Decimal = Decimal(0)


class CalculationEntry:
    """Calculation entry for final report."""

    def __init__(
        self,
        rule_type: RuleType,
        quantity: Decimal,
        amount: Decimal,
        fees: Decimal,
        new_quantity: Decimal,
        new_pool_cost: Decimal,
        gain: Decimal | None = None,
        allowable_cost: Decimal | None = None,
        bed_and_breakfast_date_index: datetime.date | None = None,
        spin_off: SpinOff | None = None,
        dividend: Dividend | None = None,
        eris: list[ExcessReportedIncome] | None = None,
    ):
        """Create calculation entry."""
        self.rule_type = rule_type
        self.quantity = quantity
        self.amount = amount
        self.allowable_cost = (
            allowable_cost if allowable_cost is not None else Decimal(0)
        )
        self.fees = fees
        self.gain = gain if gain is not None else Decimal(0)
        self.new_quantity = new_quantity
        self.new_pool_cost = new_pool_cost
        self.bed_and_breakfast_date_index = bed_and_breakfast_date_index
        self.spin_off = spin_off
        self.dividend = dividend
        self.eris = eris or []
        if self.rule_type == RuleType.EXCESS_REPORTED_INCOME:
            assert self.allowable_cost > 0, str(self)
            assert approx_equal(
                self.allowable_cost, self.amount + self.new_pool_cost
            ), f"Mismatch: {self.allowable_cost} != "
            f"{self.amount} + {self.new_pool_cost} (for {self})"
        elif self.amount >= 0 and self.rule_type not in (
            RuleType.SPIN_OFF,
            RuleType.DIVIDEND,
            RuleType.INTEREST,
            RuleType.EXCESS_REPORTED_INCOME_DISTRIBUTION,
        ):
            assert self.gain == self.amount + self.fees - self.allowable_cost, (
                f"Mismatch: {self.gain} != "
                f"{self.amount} + {self.fees} - {self.allowable_cost} (for {self})"
            )

    def __repr__(self) -> str:
        """Return print representation."""
        return f"<CalculationEntry {self!s}>"

    def __str__(self) -> str:
        """Return string representation."""
        return (
            f"{self.rule_type.name.replace('_', ' ')}, "
            f"quantity: {self.quantity}, "
            f"amount: {self.amount}, "
            f"allowable cost: {self.allowable_cost}, "
            f"fees: {self.fees}, "
            f"gain: {self.gain}, "
            f"new pool cost: {self.new_pool_cost}"
        )


class MixedFundEntry:
    """Mixed fund entry for final report."""

    def __init__(
        self,
        message: str,
        movement: dict[int, dict[MixedFundMoneyCategory, Decimal]],
        tax_movement: dict[int, dict[MixedFundMoneyCategory, Decimal]],
        mixed_fund_composition: MixedFundComposition | None = None,
        composition: list[tuple[int, MixedFundMoneyCategory, Decimal]] | None = None,
        tax_composition: list[tuple[int, MixedFundMoneyCategory, Decimal]] | None = None,
        remitted_tax_implications: dict[tuple[int, MixedFundMoneyCategory], RemittedIncomeType] | None = None,
        destination: Destination | None = None,
    ):
        """Create entry, flattening the dicts to immutable list representations."""
        self.message = message
        self.movements = get_list_representation_buckets(movement)
        self.tax_movements = get_list_representation_buckets(tax_movement)
        if composition is not None:
            self.composition = composition
        elif mixed_fund_composition is not None:
            self.composition = mixed_fund_composition.get_list_representation_buckets()
        else:
            raise ValueError("Either mixed_fund_composition or composition must be provided")
        if tax_composition is not None:
            self.tax_composition = tax_composition
        elif mixed_fund_composition is not None:
            self.tax_composition = mixed_fund_composition.get_list_representation_tax_buckets()
        else:
            raise ValueError("Either mixed_fund_composition or tax_composition must be provided")
        self.remitted_tax_implications = remitted_tax_implications
        self.destination = destination

    def movements_display(
        self,
    ) -> list[tuple[int, MixedFundMoneyCategory, Decimal, RemittedIncomeType | None, Decimal]]:
        """Return movements enriched with UK tax implication (due to remittance) type and foreign tax, for template rendering."""
        tax_lookup = {(ty, cat): ft for ty, cat, ft in self.tax_movements}
        return [
            (
                ty,
                cat,
                amount,
                self.remitted_tax_implications.get((ty, cat)) if self.remitted_tax_implications else None,
                tax_lookup.get((ty, cat), Decimal(0)),
            )
            for ty, cat, amount in self.movements
        ]

    def __repr__(self) -> str:
        """Return print representation."""
        return f"<MixedFundEntry {self!s}>"

    def __str__(self) -> str:
        """Return string representation."""
        return (
            f"{self.message}, "
            f"destination: {self.destination}, "
            f"movement: {self.movements}, "
            f"tax_movement: {self.tax_movements}, "
            f"composition: {self.composition}, "
            f"tax composition: {self.tax_composition}, "
            f"remitted_tax_implications: {self.remitted_tax_implications} "
        )


CalculationLog = dict[datetime.date, dict[str, list[CalculationEntry]]]


@dataclass
class Position:
    """A single position in the portfolio."""

    quantity: Decimal = Decimal(0)
    amount: Decimal = Decimal(0)

    def __add__(self, other: Position) -> Position:
        """Add two positions."""
        return Position(
            self.quantity + other.quantity,
            self.amount + other.amount,
        )

    def __sub__(self, other: Position) -> Position:
        """Subtract two positions."""
        return Position(
            self.quantity - other.quantity,
            self.amount - other.amount,
        )

    def __str__(self) -> str:
        """Return string representation."""
        return str(round_decimal(self.quantity, 2))


class PortfolioEntry:
    """A single symbol entry for the portfolio in the final report."""

    def __init__(
        self,
        symbol: str,
        quantity: Decimal,
        amount: Decimal,
        unrealized_gains: Decimal | None,
    ):
        """Create portfolio entry."""
        self.symbol = symbol
        self.quantity = quantity
        self.amount = amount
        self.unrealized_gains = unrealized_gains

    def unrealized_gains_str(self) -> str:
        """Format the unrealized gains to show in the report."""
        if self.unrealized_gains is None:
            str_val = "unknown"
        else:
            str_val = f"£{round_decimal(self.unrealized_gains, 2)}"

        return f" (unrealized gains: {str_val})"

    def __repr__(self) -> str:
        """Return print representation."""
        return f"<PortfolioEntry {self!s}>"

    def __str__(self) -> str:
        """Return string representation."""
        return (
            f"  {self.symbol}: quantity: {round_decimal(self.quantity, 2)}, "
            f"cost: £{round_decimal(self.amount, 2)}"
        )


_UNSET = object()

# The underlying nature of each mixed fund money category: whether it represents
# income-type or capital-gain-type money, regardless of whether remitting it actually
# creates a UK tax implication due to remittance (which also depends on the tax filing
# basis of the year -- money can still be taxable via a different route, e.g. it was
# already taxed on the arising basis, taxed as ordinary UK income, or via the TRF charge).
_CATEGORY_NATURE: dict[MixedFundMoneyCategory, RemittedIncomeType] = {
    MixedFundMoneyCategory.EMPLOYMENT_INCOME: RemittedIncomeType.INCOME,
    MixedFundMoneyCategory.RELEVANT_FOREIGN_EARNINGS: RemittedIncomeType.INCOME,
    MixedFundMoneyCategory.FOREIGN_SPECIFIC_EMPLOYMENT_INCOME: RemittedIncomeType.INCOME,
    MixedFundMoneyCategory.RELEVANT_FOREIGN_INCOME: RemittedIncomeType.INCOME,
    MixedFundMoneyCategory.FOREIGN_CHARGEABLE_GAINS: RemittedIncomeType.CAPITAL_GAIN,
    MixedFundMoneyCategory.EMPLOYMENT_INCOME_SUBJECT_TO_A_FOREIGN_FAX: RemittedIncomeType.INCOME,
    MixedFundMoneyCategory.RELEVANT_FOREIGN_INCOME_SUBJECT_TO_A_FOREIGN_FAX: RemittedIncomeType.INCOME,
    MixedFundMoneyCategory.FOREIGN_CHARGEABLE_GAINS_SUBJECT_TO_A_FOREIGN_FAX: RemittedIncomeType.CAPITAL_GAIN,
    MixedFundMoneyCategory.OTHER_INCOME: RemittedIncomeType.INCOME,
}


@dataclass
class CapitalGainsReport:
    """Store calculated report."""

    tax_year: int
    portfolio: list[PortfolioEntry]
    disposal_count: int
    disposed_symbols: set[str]
    disposal_proceeds: Decimal
    allowable_costs: Decimal
    capital_gain: Decimal
    capital_loss: Decimal
    capital_gain_allowance: Decimal | None
    dividend_allowance: Decimal | None
    calculation_log: CalculationLog
    calculation_log_yields: CalculationLog
    total_uk_interest: Decimal
    total_foreign_interest: Decimal
    show_unrealized_gains: bool
    mixed_funds_log: dict
    trf_declarations: list = field(default_factory=list)
    tax_filings: object = field(default=None, repr=False)
    # SA108 reports cryptoasset disposals separately; the listed securities
    # totals are derived as the remainder (see listed_totals).
    crypto_totals: CgtAssetClassTotals = field(default_factory=CgtAssetClassTotals)
    mixed_funds_recap_log: dict[str, list[MixedFundEntry]] = field(init=False)
    mixed_funds_pre_post_2025_columns: dict[
        str, list[tuple[Period, MixedFundMoneyCategory]]
    ] = field(init=False)
    mixed_funds_columns: dict[str, list[tuple[int, MixedFundMoneyCategory]]] = field(init=False)
    mixed_funds_type_columns: dict[str, list[MixedFundMoneyCategory]] = field(init=False)

    def __post_init__(self):

        self.mixed_funds_recap_log = dict()
        self.mixed_funds_pre_post_2025_columns = dict()
        self.mixed_funds_columns = dict()
        self.mixed_funds_type_columns = dict()

        for broker in self.mixed_funds_log.keys():
            mixed_fund_log = self.mixed_funds_log[broker]
            if mixed_fund_log:
                start_entry = mixed_fund_log[0]
                end_entry = mixed_fund_log[-1]
                self.mixed_funds_recap_log[broker] = [
                    MixedFundEntry(
                        message="Composition at the beginning of the tax year",
                        movement={},
                        tax_movement={},
                        composition=start_entry.composition,
                        tax_composition=start_entry.tax_composition,
                    ),
                    MixedFundEntry(
                        message="Composition at the end of the tax year",
                        movement={},
                        tax_movement={},
                        composition=end_entry.composition,
                        tax_composition=end_entry.tax_composition,
                    ),
                ]
            else:
                self.mixed_funds_recap_log[broker] = []
            pre_post_2025_columns = []
            columns = []
            categories = []
            for entry in mixed_fund_log:
                composition = entry.composition
                for (tax_year, category, amount) in composition:
                    period = get_period(tax_year, self.tax_filings)
                    if amount and (period, category) not in pre_post_2025_columns:
                        pre_post_2025_columns.append((period, category))
                    if amount and (tax_year, category) not in columns:
                        columns.append((tax_year, category))
                    if amount and category not in categories:
                        categories.append(category)
            pre_post_2025_columns = sorted(
                pre_post_2025_columns,
                key=lambda x: (_PERIOD_ORDER[x[0]], x[1].value),
            )
            self.mixed_funds_pre_post_2025_columns[broker] = pre_post_2025_columns
            columns = sorted(columns, key=lambda x:  (-x[0], x[1].value) )
            self.mixed_funds_columns[broker] = columns
            self.mixed_funds_type_columns[broker] = sorted(
                categories,
                key=lambda category: category.value,
            )


    def _filter_calculation_log(
        self, calculation_log: CalculationLog, rule_type: RuleType
    ) -> Generator[CalculationEntry]:
        for data in calculation_log.values():
            for entry_list in data.values():
                for entry in entry_list:
                    if entry.rule_type == rule_type:
                        yield entry

    def total_unrealized_gains(self) -> Decimal:
        """Total unrealized gains across portfolio."""
        return sum(
            (
                h.unrealized_gains
                for h in self.portfolio
                if h.unrealized_gains is not None
            ),
            Decimal(0),
        )

    @property
    def listed_totals(self) -> CgtAssetClassTotals:
        """CGT totals for everything that is not a cryptoasset."""
        return CgtAssetClassTotals(
            disposal_count=self.disposal_count - self.crypto_totals.disposal_count,
            disposal_proceeds=(
                self.disposal_proceeds - self.crypto_totals.disposal_proceeds
            ),
            allowable_costs=self.allowable_costs - self.crypto_totals.allowable_costs,
            capital_gain=self.capital_gain - self.crypto_totals.capital_gain,
            capital_loss=self.capital_loss - self.crypto_totals.capital_loss,
        )

    def total_gain(self) -> Decimal:
        """Total capital gain."""
        return self.capital_gain + self.capital_loss

    def taxable_gain(self) -> Decimal:
        """Taxable gain with current allowance."""
        assert self.capital_gain_allowance is not None
        return max(Decimal(0), self.total_gain() - self.capital_gain_allowance)

    def total_eri_amount(self, is_interest: bool) -> Decimal:
        """Total dividends amount just from ERI."""
        total = Decimal(0)
        for item in self._filter_calculation_log(
            self.calculation_log_yields, RuleType.EXCESS_REPORTED_INCOME_DISTRIBUTION
        ):
            assert item.eris
            assert len(item.eris) == 1
            if item.eris[0].is_interest == is_interest:
                total += item.amount
        return total

    def total_dividends_amount(self) -> Decimal:
        """Total dividends amount."""
        total = Decimal(0)
        for item in self._filter_calculation_log(
            self.calculation_log_yields, RuleType.DIVIDEND
        ):
            assert item.dividend is not None
            if not item.dividend.is_interest:
                total += item.amount

        total += self.total_eri_amount(is_interest=False)

        return total

    def total_dividend_taxes_in_tax_treaties_amount(self) -> Decimal:
        """Total taxes to be reclaimed due to tax treaties."""
        return sum(
            (
                summary.treaty_allowance
                for summary in self.dividend_summary_by_country().values()
            ),
            Decimal(0),
        )

    def dividend_summary_by_country(self) -> dict[str, DividendCountrySummary]:
        """Foreign dividends, tax paid and treaty allowance per country."""
        by_country: defaultdict[str, DividendCountrySummary] = defaultdict(
            DividendCountrySummary
        )
        for item in self._filter_calculation_log(
            self.calculation_log_yields, RuleType.DIVIDEND
        ):
            assert item.dividend is not None
            dividend = item.dividend
            if dividend.is_interest or dividend.country is None:
                continue
            summary = by_country[dividend.country]
            summary.amount += dividend.amount
            summary.tax_paid += -dividend.tax_at_source
            summary.treaty_allowance += dividend.tax_treaty_amount
        return dict(sorted(by_country.items()))

    def total_dividend_taxable_gain(self) -> Decimal:
        """Total taxable gain after all allowances."""
        return max(
            Decimal(0),
            self.total_dividends_amount()
            - (self.dividend_allowance or Decimal(0))
            - self.total_dividend_taxes_in_tax_treaties_amount(),
        )

    def _iter_transfer_out(
        self,
        broker: str | None = None,
    ) -> Generator[tuple[Destination, int, MixedFundMoneyCategory, Decimal, Decimal, RemittedIncomeType | None]]:
        """Yield (destination, tax_year, category, amount, foreign_tax, uk_implication) for every transfer-out movement.

        If broker is given, only that mixed fund's log is considered; otherwise all are.
        """
        logs = (
            [self.mixed_funds_log[broker]]
            if broker is not None
            else self.mixed_funds_log.values()
        )
        for mixed_fund_log in logs:
            for entry in mixed_fund_log:
                if entry.destination is None:
                    continue
                tax_lookup = {(ty, cat): ft for ty, cat, ft in entry.tax_movements}
                for tax_year, category, amount in entry.movements:
                    foreign_tax = tax_lookup.get((tax_year, category), Decimal(0))
                    uk_implication = (
                        entry.remitted_tax_implications.get((tax_year, category))
                        if entry.remitted_tax_implications
                        else None
                    )
                    yield entry.destination, tax_year, category, amount, foreign_tax, uk_implication

    def _sum_transfer_out(
        self,
        broker: str | None = None,
        destination: Destination | None = None,
        uk_implication=_UNSET,
        has_foreign_tax: bool | None = None,
        pre_2025: bool | None = None,
        category: MixedFundMoneyCategory | None = None,
        nature: RemittedIncomeType | None = None,
        period: Period | None = None,
    ) -> Decimal:
        """Sum movement amounts across transfer-out entries, with optional filters.

        uk_implication=_UNSET matches any implication; None matches movements with no UK tax
        implication due to remittance (the money may still be taxable via another route).
        nature filters by the underlying income/capital-gain nature of the category (see _CATEGORY_NATURE),
        independently of whether that movement actually carries a UK tax implication due to remittance.
        Returned total is negative (withdrawals); callers negate for display.
        """
        total = Decimal(0)
        for dest, tax_year, cat, amount, foreign_tax, impl in self._iter_transfer_out(broker):
            if destination is not None and dest != destination:
                continue
            if uk_implication is not _UNSET and impl != uk_implication:
                continue
            if has_foreign_tax is not None and bool(foreign_tax) != has_foreign_tax:
                continue
            if pre_2025 is not None and tax_year == TRF_CAPITAL_TAX_YEAR:
                continue
            if pre_2025 is not None and (tax_year < 2025) != pre_2025:
                continue
            if period is not None and get_period(tax_year, self.tax_filings) != period:
                continue
            if category is not None and cat != category:
                continue
            if nature is not None and _CATEGORY_NATURE.get(cat) != nature:
                continue
            total += amount
        return total

    def _sum_transfer_out_with_tax(
        self,
        broker: str | None = None,
        destination: Destination | None = None,
        uk_implication=_UNSET,
        has_foreign_tax: bool | None = None,
        pre_2025: bool | None = None,
        category: MixedFundMoneyCategory | None = None,
        nature: RemittedIncomeType | None = None,
        period: Period | None = None,
    ) -> tuple[Decimal, Decimal]:
        """Like _sum_transfer_out but also accumulates foreign tax. Returns (amount, foreign_tax), both negative."""
        total = Decimal(0)
        tax_total = Decimal(0)
        for dest, tax_year, cat, amount, foreign_tax, impl in self._iter_transfer_out(broker):
            if destination is not None and dest != destination:
                continue
            if uk_implication is not _UNSET and impl != uk_implication:
                continue
            if has_foreign_tax is not None and bool(foreign_tax) != has_foreign_tax:
                continue
            if pre_2025 is not None and tax_year == TRF_CAPITAL_TAX_YEAR:
                continue
            if pre_2025 is not None and (tax_year < 2025) != pre_2025:
                continue
            if period is not None and get_period(tax_year, self.tax_filings) != period:
                continue
            if category is not None and cat != category:
                continue
            if nature is not None and _CATEGORY_NATURE.get(cat) != nature:
                continue
            total += amount
            tax_total += foreign_tax
        return total, tax_total

    def transferred_out_total(self, broker: str | None = None) -> Decimal:
        """Total of all transfer-out movements (UK remittances + overseas)."""
        return -self._sum_transfer_out(broker)

    def remitted_total(self, broker: str | None = None) -> Decimal:
        """Total remitted to the UK."""
        return -self._sum_transfer_out(broker, destination=Destination.UK)

    def transferred_overseas_total(self, broker: str | None = None) -> Decimal:
        """Total transferred overseas."""
        return -self._sum_transfer_out(broker, destination=Destination.OVERSEAS)

    def remitted_income(self, broker: str | None = None) -> Decimal:
        """Total income-type money remitted to the UK, regardless of UK tax implication due to remittance."""
        return -self._sum_transfer_out(broker, destination=Destination.UK, nature=RemittedIncomeType.INCOME)

    def remitted_income_no_tax_implication(self, broker: str | None = None) -> Decimal:
        """Remitted income-type money with no UK tax implication due to remittance (may still be taxable via another route)."""
        return -self._sum_transfer_out(
            broker, destination=Destination.UK, nature=RemittedIncomeType.INCOME, uk_implication=None
        )

    def remitted_income_tax_implication(self, broker: str | None = None) -> Decimal:
        """Remitted income-type money that creates a UK income tax implication due to remittance."""
        return -self._sum_transfer_out(
            broker, destination=Destination.UK, nature=RemittedIncomeType.INCOME, uk_implication=RemittedIncomeType.INCOME
        )

    def remitted_income_tax_implication_no_relief(self, broker: str | None = None) -> Decimal:
        """Remitted income with a UK tax implication due to remittance and no associated foreign tax credit."""
        return -self._sum_transfer_out(
            broker,
            destination=Destination.UK,
            nature=RemittedIncomeType.INCOME,
            uk_implication=RemittedIncomeType.INCOME,
            has_foreign_tax=False,
        )

    def remitted_income_tax_implication_with_relief(self, broker: str | None = None) -> tuple[Decimal, Decimal]:
        """Remitted income with a UK tax implication due to remittance that carries a foreign tax credit. Returns (amount, foreign_tax_paid)."""
        total, tax = self._sum_transfer_out_with_tax(
            broker,
            destination=Destination.UK,
            nature=RemittedIncomeType.INCOME,
            uk_implication=RemittedIncomeType.INCOME,
            has_foreign_tax=True,
        )
        return -total, -tax

    def remitted_gains(self, broker: str | None = None) -> Decimal:
        """Total capital-gain-type money remitted to the UK, regardless of UK tax implication due to remittance."""
        return -self._sum_transfer_out(broker, destination=Destination.UK, nature=RemittedIncomeType.CAPITAL_GAIN)

    def remitted_gains_no_tax_implication(self, broker: str | None = None) -> Decimal:
        """Remitted gain-type money with no UK tax implication due to remittance (may still be taxable via another route)."""
        return -self._sum_transfer_out(
            broker, destination=Destination.UK, nature=RemittedIncomeType.CAPITAL_GAIN, uk_implication=None
        )

    def remitted_gains_tax_implication(self, broker: str | None = None) -> Decimal:
        """Remitted gain-type money that creates a UK capital gains tax implication due to remittance."""
        return -self._sum_transfer_out(
            broker,
            destination=Destination.UK,
            nature=RemittedIncomeType.CAPITAL_GAIN,
            uk_implication=RemittedIncomeType.CAPITAL_GAIN,
        )

    def remitted_gains_tax_implication_no_relief(self, broker: str | None = None) -> Decimal:
        """Remitted gains with a UK tax implication due to remittance and no associated foreign tax credit."""
        return -self._sum_transfer_out(
            broker,
            destination=Destination.UK,
            nature=RemittedIncomeType.CAPITAL_GAIN,
            uk_implication=RemittedIncomeType.CAPITAL_GAIN,
            has_foreign_tax=False,
        )

    def remitted_gains_tax_implication_with_relief(self, broker: str | None = None) -> tuple[Decimal, Decimal]:
        """Remitted gains with a UK tax implication due to remittance that carry a foreign tax credit. Returns (amount, foreign_tax_paid)."""
        total, tax = self._sum_transfer_out_with_tax(
            broker,
            destination=Destination.UK,
            nature=RemittedIncomeType.CAPITAL_GAIN,
            uk_implication=RemittedIncomeType.CAPITAL_GAIN,
            has_foreign_tax=True,
        )
        return -total, -tax

    def remitted_pre_2025(self, broker: str | None = None) -> Decimal:
        """Total remitted to the UK drawn from pre-2025 tax year buckets."""
        return -self._sum_transfer_out(broker, destination=Destination.UK, pre_2025=True)

    def remitted_post_2025(self, broker: str | None = None) -> Decimal:
        """Total remitted to the UK drawn from 2025-and-later tax year buckets."""
        return -self._sum_transfer_out(broker, destination=Destination.UK, pre_2025=False)

    def transferred_overseas_pre_2025(self, broker: str | None = None) -> Decimal:
        """Total transferred overseas drawn from pre-2025 tax year buckets."""
        return -self._sum_transfer_out(broker, destination=Destination.OVERSEAS, pre_2025=True)

    def transferred_overseas_post_2025(self, broker: str | None = None) -> Decimal:
        """Total transferred overseas drawn from 2025-and-later tax year buckets."""
        return -self._sum_transfer_out(broker, destination=Destination.OVERSEAS, pre_2025=False)

    def remitted_from_trf_capital(self, broker: str | None = None) -> Decimal:
        """Total remitted to the UK drawn from TRF Capital."""
        return -self._sum_transfer_out(
            broker, destination=Destination.UK, category=MixedFundMoneyCategory.TRF_CAPITAL
        )

    def transferred_overseas_from_trf_capital(self, broker: str | None = None) -> Decimal:
        """Total transferred overseas drawn from TRF Capital."""
        return -self._sum_transfer_out(
            broker, destination=Destination.OVERSEAS, category=MixedFundMoneyCategory.TRF_CAPITAL
        )

    def trf_capital_balance(self, broker: str) -> Decimal:
        """TRF Capital balance at the end of the tax year."""
        recap = self.mixed_funds_recap_log.get(broker)
        if not recap:
            return Decimal(0)
        for _, category, amount in recap[-1].composition:
            if category == MixedFundMoneyCategory.TRF_CAPITAL:
                return amount
        return Decimal(0)

    def breakdown_by_category_with_tax(
        self,
        broker: str | None = None,
        destination: Destination | None = None,
        uk_implication=_UNSET,
        has_foreign_tax: bool | None = None,
        pre_2025: bool | None = None,
        nature: RemittedIncomeType | None = None,
        period: Period | None = None,
    ) -> dict[MixedFundMoneyCategory, tuple[Decimal, Decimal]]:
        """Per-category (amount, foreign_tax) breakdown of transfer-out movements matching the given filters.

        Both values in the returned tuples are positive. Categories with no matching movement
        (amount and foreign_tax both zero) are omitted.
        """
        result: dict[MixedFundMoneyCategory, tuple[Decimal, Decimal]] = {}
        for cat in MixedFundMoneyCategory:
            amount, tax = self._sum_transfer_out_with_tax(
                broker,
                destination=destination,
                uk_implication=uk_implication,
                has_foreign_tax=has_foreign_tax,
                pre_2025=pre_2025,
                category=cat,
                nature=nature,
                period=period,
            )
            if amount or tax:
                result[cat] = (-amount, -tax)
        return result

    def breakdown_by_category(
        self,
        broker: str | None = None,
        destination: Destination | None = None,
        uk_implication=_UNSET,
        has_foreign_tax: bool | None = None,
        pre_2025: bool | None = None,
        nature: RemittedIncomeType | None = None,
        period: Period | None = None,
    ) -> dict[MixedFundMoneyCategory, Decimal]:
        """Per-category breakdown of transfer-out amounts matching the given filters. See breakdown_by_category_with_tax."""
        return {
            cat: amount
            for cat, (amount, _tax) in self.breakdown_by_category_with_tax(
                broker,
                destination=destination,
                uk_implication=uk_implication,
                has_foreign_tax=has_foreign_tax,
                pre_2025=pre_2025,
                nature=nature,
                period=period,
            ).items()
        }

    def remitted_by_period(self, broker: str, period: Period) -> Decimal:
        """Total remitted to the UK drawn from a specific Period bucket group."""
        return -self._sum_transfer_out(broker, destination=Destination.UK, period=period)

    def transferred_overseas_by_period(self, broker: str, period: Period) -> Decimal:
        """Total transferred overseas drawn from a specific Period bucket group."""
        return -self._sum_transfer_out(broker, destination=Destination.OVERSEAS, period=period)

    def __repr__(self) -> str:
        """Return string representation."""
        return f"<CalculationEntry: {self!s}>"

    def __str__(self) -> str:
        """Return string representation."""
        out = f"Portfolio at the end of {self.tax_year}/{self.tax_year + 1} tax year:\n"
        for entry in self.portfolio:
            if entry.quantity > 0:
                unrealized_gains_str = (
                    entry.unrealized_gains_str() if self.show_unrealized_gains else ""
                )
                out += f"{entry!s}{unrealized_gains_str}\n"
        eris = list(
            self._filter_calculation_log(
                self.calculation_log_yields,
                RuleType.EXCESS_REPORTED_INCOME_DISTRIBUTION,
            )
        )
        out += f"For tax year {self.tax_year}/{self.tax_year + 1}:\n"
        if eris:
            out += "Excess Reported Income:\n"
            for item in self._filter_calculation_log(
                self.calculation_log_yields,
                RuleType.EXCESS_REPORTED_INCOME_DISTRIBUTION,
            ):
                assert item.eris
                assert len(item.eris) == 1
                dist_type = "interest" if item.eris[0].is_interest else "dividend"
                out += f"  {item.eris[0].symbol}: £{round_decimal(item.amount, 2)} "
                out += f"(included as {dist_type})\n"

        out += f"Number of disposals: {self.disposal_count}\n"
        out += f"Disposed securities: {sorted(self.disposed_symbols)}\n"
        out += f"Disposal proceeds: £{self.disposal_proceeds}\n"
        out += f"Allowable costs: £{self.allowable_costs}\n"
        out += f"Capital gain: £{self.capital_gain}\n"
        out += f"Capital loss: £{-self.capital_loss}\n"
        if self.crypto_totals.disposal_count:
            out += "CGT split for SA108:\n"
            for label, totals in (
                ("Listed securities", self.listed_totals),
                ("Cryptoassets", self.crypto_totals),
            ):
                out += (
                    f"  {label}: {totals.disposal_count} disposals, "
                    f"proceeds £{round_decimal(totals.disposal_proceeds, 2)}, "
                    f"allowable costs £{round_decimal(totals.allowable_costs, 2)}, "
                    "gains in the year before losses "
                    f"£{round_decimal(totals.capital_gain, 2)}, "
                    f"losses in the year £{round_decimal(-totals.capital_loss, 2)}\n"
                )
        out += f"Total capital gain: £{self.total_gain()}\n"
        if self.capital_gain_allowance is not None:
            out += f"Taxable capital gain: £{self.taxable_gain()}\n"
        else:
            out += "WARNING: Missing allowance for this tax year\n"
        if self.show_unrealized_gains:
            total_unrealized_gains = round_decimal(self.total_unrealized_gains(), 2)
            out += f"Total unrealized gains: £{total_unrealized_gains}\n"
            if any(h.unrealized_gains is None for h in self.portfolio):
                out += (
                    "WARNING: Some unrealized gains couldn't be calculated."
                    " Take a look at the symbols with unknown unrealized gains above"
                    " and factor in their prices.\n"
                )
        out += (
            "Total dividends proceeds: "
            f"£{round_decimal(self.total_dividends_amount(), 2)}\n"
        )
        if self.dividend_allowance is not None:
            out += (
                "Total amount of dividends tax yearly allowance: "
                f"£{round_decimal(self.dividend_allowance, 2)}\n"
            )
        if (
            self.dividend_allowance is not None
            or self.total_dividend_taxes_in_tax_treaties_amount() > 0
        ):
            out += (
                "Total taxable dividends proceeds: "
                f"£{round_decimal(self.total_dividend_taxable_gain(), 2)}\n"
            )
        out += f"Total UK interest proceeds: £{self.total_uk_interest}\n"
        out += f"Total foreign interest proceeds: £{self.total_foreign_interest}\n"

        by_country = self.dividend_summary_by_country()
        if by_country:
            out += "Foreign dividends by country:\n"
            for country, summary in by_country.items():
                out += (
                    f"  {country}: dividends £{round_decimal(summary.amount, 2)}, "
                    f"foreign tax paid £{round_decimal(summary.tax_paid, 2)}, "
                    "tax allowance from treaty "
                    f"£{round_decimal(summary.treaty_allowance, 2)}\n"
                )

        out += "REMITTANCE RESULTS PER MIXED FUND:\n"
        for broker in self.mixed_funds_log:
            out += f"{broker}:\n"
            out += f"  Total remitted income: £{round_decimal(self.remitted_income(broker), 2)}\n"
            out += f"  Total remitted income without UK tax implication: £{round_decimal(self.remitted_income_no_tax_implication(broker), 2)}\n"
            out += f"  Total remitted income with UK tax implication: £{round_decimal(self.remitted_income_tax_implication(broker), 2)}\n"
            out += f"    - without tax relief: £{round_decimal(self.remitted_income_tax_implication_no_relief(broker), 2)}\n"
            out += f"    - with tax relief: £{round_decimal(self.remitted_income_tax_implication_with_relief(broker)[0], 2)} -- foreign tax paid: £{round_decimal(self.remitted_income_tax_implication_with_relief(broker)[1], 2)}\n"
            out += f"  Total remitted gains: £{round_decimal(self.remitted_gains(broker), 2)}\n"
            out += f"  Total remitted gains without UK tax implication: £{round_decimal(self.remitted_gains_no_tax_implication(broker), 2)}\n"
            out += f"  Total remitted gains with UK tax implication: £{round_decimal(self.remitted_gains_tax_implication(broker), 2)}\n"
            out += f"    - without tax relief: £{round_decimal(self.remitted_gains_tax_implication_no_relief(broker), 2)}\n"
            out += f"    - with tax relief: £{round_decimal(self.remitted_gains_tax_implication_with_relief(broker)[0], 2)} -- foreign tax paid: £{round_decimal(self.remitted_gains_tax_implication_with_relief(broker)[1], 2)}\n"
            out += f"  Total remitted from TRF Capital: £{round_decimal(self.remitted_from_trf_capital(broker), 2)}\n"
            out += f"  Total transferred overseas from TRF Capital: £{round_decimal(self.transferred_overseas_from_trf_capital(broker), 2)}\n"
            out += f"  TRF Capital balance at end of year: £{round_decimal(self.trf_capital_balance(broker), 2)}\n"

        return out


class MixedFundsReport:
    pass
