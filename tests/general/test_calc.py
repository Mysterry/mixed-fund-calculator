"""Unit and integration tests."""

from __future__ import annotations

import datetime
from decimal import Decimal
from pathlib import Path
import subprocess
import sys
from typing import TYPE_CHECKING

import pytest

from cgt_calc.currency_converter import CurrencyConverter
from cgt_calc.current_price_fetcher import CurrentPriceFetcher
from cgt_calc.initial_prices import InitialPrices
from cgt_calc.isin_converter import IsinConverter
from cgt_calc.main import CapitalGainsCalculator
from cgt_calc.model import (
    ActionType,
    BrokerTransaction,
    CalculationEntry,
    CapitalGainsReport,
    Dividend,
    ForeignCurrencyAmount,
    RuleType,
    TaxTreaty,
)
from cgt_calc.spin_off_handler import SpinOffHandler
from cgt_calc.util import round_decimal
from tests.utils import build_cmd

from .calc_test_data import calc_basic_data
from .calc_test_data_2 import calc_basic_data_2

if TYPE_CHECKING:
    from cgt_calc.model import CalculationLog


def get_report(
    calculator: CapitalGainsCalculator, broker_transactions: list[BrokerTransaction]
) -> CapitalGainsReport:
    """Get calculation report."""
    calculator.convert_to_hmrc_transactions(broker_transactions)
    return calculator.calculate_capital_gain()


def test_main_prints_help_when_no_arguments() -> None:
    """Ensure CLI prints help text when invoked without arguments."""
    result = subprocess.run(
        [sys.executable, "-m", "cgt_calc.main"],
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode == 0
    assert "usage:" in result.stdout
    assert "Calculate UK capital gains" in result.stdout


def test_mixed_fund_report_exposes_type_only_columns_and_recap() -> None:
    """Mixed fund report should expose both year/type, recap and type-only columns."""

    from cgt_calc.model import (
        CapitalGainsReport,
        MixedFundComposition,
        MixedFundEntry,
        MixedFundMoneyCategory,
        Period,
    )

    composition = MixedFundComposition("Schwab")
    composition.add_money(2024, MixedFundMoneyCategory.EMPLOYMENT_INCOME, Decimal(10))
    composition.add_money(2025, MixedFundMoneyCategory.EMPLOYMENT_INCOME, Decimal(5))
    composition.add_money(
        2025, MixedFundMoneyCategory.RELEVANT_FOREIGN_INCOME, Decimal(7)
    )

    report = CapitalGainsReport(
        tax_year=2026,
        portfolio=[],
        disposal_count=0,
        disposed_symbols=set(),
        disposal_proceeds=Decimal(0),
        allowable_costs=Decimal(0),
        capital_gain=Decimal(0),
        capital_loss=Decimal(0),
        capital_gain_allowance=None,
        dividend_allowance=None,
        calculation_log={},
        calculation_log_yields={},
        total_uk_interest=Decimal(0),
        total_foreign_interest=Decimal(0),
        show_unrealized_gains=False,
        mixed_funds_log={
            "Schwab": [
                MixedFundEntry(
                    message="start",
                    movement={},
                    tax_movement={},
                    composition=[
                        (2024, MixedFundMoneyCategory.EMPLOYMENT_INCOME, Decimal(10))
                    ],
                    tax_composition=[
                        (2024, MixedFundMoneyCategory.EMPLOYMENT_INCOME, Decimal(2))
                    ],
                ),
                MixedFundEntry(
                    message="end",
                    movement={},
                    tax_movement={},
                    composition=[
                        (2025, MixedFundMoneyCategory.EMPLOYMENT_INCOME, Decimal(5)),
                        (
                            2025,
                            MixedFundMoneyCategory.RELEVANT_FOREIGN_INCOME,
                            Decimal(7),
                        ),
                        (2024, MixedFundMoneyCategory.EMPLOYMENT_INCOME, Decimal(3)),
                    ],
                    tax_composition=[
                        (2025, MixedFundMoneyCategory.EMPLOYMENT_INCOME, Decimal(1)),
                        (
                            2025,
                            MixedFundMoneyCategory.RELEVANT_FOREIGN_INCOME,
                            Decimal(4),
                        ),
                        (2024, MixedFundMoneyCategory.EMPLOYMENT_INCOME, Decimal(1)),
                    ],
                )
            ]
        },
    )

    assert report.mixed_funds_columns["Schwab"] == [
        (2025, MixedFundMoneyCategory.EMPLOYMENT_INCOME),
        (2025, MixedFundMoneyCategory.RELEVANT_FOREIGN_INCOME),
        (2024, MixedFundMoneyCategory.EMPLOYMENT_INCOME),
    ]
    assert report.mixed_funds_pre_post_2025_columns["Schwab"] == [
        (Period.POST_2025, MixedFundMoneyCategory.EMPLOYMENT_INCOME),
        (Period.POST_2025, MixedFundMoneyCategory.RELEVANT_FOREIGN_INCOME),
        (Period.PRE_2025_ARISING, MixedFundMoneyCategory.EMPLOYMENT_INCOME),
    ]
    assert report.mixed_funds_type_columns["Schwab"] == [
        MixedFundMoneyCategory.EMPLOYMENT_INCOME,
        MixedFundMoneyCategory.RELEVANT_FOREIGN_INCOME,
    ]
    assert [entry.message for entry in report.mixed_funds_recap_log["Schwab"]] == [
        "Composition at the beginning of the tax year",
        "Composition at the end of the tax year",
    ]
    assert report.mixed_funds_recap_log["Schwab"][0].composition == [
        (2024, MixedFundMoneyCategory.EMPLOYMENT_INCOME, Decimal(10))
    ]
    assert report.mixed_funds_recap_log["Schwab"][1].composition == [
        (2025, MixedFundMoneyCategory.EMPLOYMENT_INCOME, Decimal(5)),
        (2025, MixedFundMoneyCategory.RELEVANT_FOREIGN_INCOME, Decimal(7)),
        (2024, MixedFundMoneyCategory.EMPLOYMENT_INCOME, Decimal(3)),
    ]


def test_mixed_fund_pre_post_2025_columns_handle_pre_2025_years() -> None:
    """Pre/post-2025 recap should still work when only pre-2025 buckets exist."""

    from cgt_calc.model import (
        CapitalGainsReport,
        MixedFundEntry,
        MixedFundMoneyCategory,
        Period,
    )

    report = CapitalGainsReport(
        tax_year=2024,
        portfolio=[],
        disposal_count=0,
        disposed_symbols=set(),
        disposal_proceeds=Decimal(0),
        allowable_costs=Decimal(0),
        capital_gain=Decimal(0),
        capital_loss=Decimal(0),
        capital_gain_allowance=None,
        dividend_allowance=None,
        calculation_log={},
        calculation_log_yields={},
        total_uk_interest=Decimal(0),
        total_foreign_interest=Decimal(0),
        show_unrealized_gains=False,
        mixed_funds_log={
            "Schwab": [
                MixedFundEntry(
                    message="start",
                    movement={},
                    tax_movement={},
                    composition=[
                        (2024, MixedFundMoneyCategory.EMPLOYMENT_INCOME, Decimal(10))
                    ],
                    tax_composition=[
                        (2024, MixedFundMoneyCategory.EMPLOYMENT_INCOME, Decimal(1))
                    ],
                )
            ]
        },
    )

    assert report.mixed_funds_pre_post_2025_columns["Schwab"] == [
        (Period.PRE_2025_ARISING, MixedFundMoneyCategory.EMPLOYMENT_INCOME)
    ]


def test_dividend_summary_is_grouped_by_country() -> None:
    """Dividends, tax paid and treaty allowance should be summed per country."""

    usa_treaty = TaxTreaty("USA", Decimal("0.15"))
    poland_treaty = TaxTreaty("Poland", Decimal("0.1"))

    report = CapitalGainsReport(
        tax_year=2026,
        portfolio=[],
        disposal_count=0,
        disposed_symbols=set(),
        disposal_proceeds=Decimal(0),
        allowable_costs=Decimal(0),
        capital_gain=Decimal(0),
        capital_loss=Decimal(0),
        capital_gain_allowance=None,
        dividend_allowance=Decimal(500),
        calculation_log={},
        calculation_log_yields={
            datetime.date(2026, 6, 1): {
                "dividend$AAA": [
                    CalculationEntry(
                        rule_type=RuleType.DIVIDEND,
                        quantity=Decimal(1),
                        amount=Decimal("100"),
                        new_quantity=Decimal(1),
                        new_pool_cost=Decimal(0),
                        fees=Decimal(0),
                        dividend=Dividend(
                            date=datetime.date(2026, 6, 1),
                            symbol="AAA",
                            amount=Decimal("100"),
                            tax_at_source=Decimal("-15"),
                            is_interest=False,
                            tax_treaty=usa_treaty,
                            country="USA",
                        ),
                    )
                ],
                "dividend$BBB": [
                    CalculationEntry(
                        rule_type=RuleType.DIVIDEND,
                        quantity=Decimal(1),
                        amount=Decimal("50"),
                        new_quantity=Decimal(1),
                        new_pool_cost=Decimal(0),
                        fees=Decimal(0),
                        dividend=Dividend(
                            date=datetime.date(2026, 6, 2),
                            symbol="BBB",
                            amount=Decimal("50"),
                            tax_at_source=Decimal("-9.5"),
                            is_interest=False,
                            tax_treaty=poland_treaty,
                            country="Poland",
                        ),
                    )
                ],
            }
        },
        total_uk_interest=Decimal(0),
        total_foreign_interest=Decimal(0),
        show_unrealized_gains=False,
        mixed_funds_log={},
    )

    assert report.total_dividend_taxes_in_tax_treaties_amount() == Decimal("20")
    summary = report.dividend_summary_by_country()
    assert list(summary) == ["Poland", "USA"]
    assert summary["USA"].amount == Decimal("100")
    assert summary["USA"].tax_paid == Decimal("15")
    assert summary["USA"].treaty_allowance == Decimal("15")
    assert summary["Poland"].amount == Decimal("50")
    assert summary["Poland"].tax_paid == Decimal("9.5")
    assert summary["Poland"].treaty_allowance == Decimal("5")
    assert "Foreign dividends by country" in str(report)


def _make_dividend_calculator(
    date: datetime.date, currency: str
) -> CapitalGainsCalculator:
    """Build a minimal calculator for dividend treaty tests."""
    currency_converter = CurrencyConverter(None, {date: {currency: Decimal(1)}})
    price_fetcher = CurrentPriceFetcher(currency_converter, {}, {})
    return CapitalGainsCalculator(
        2026,
        currency_converter,
        IsinConverter(),
        price_fetcher,
        SpinOffHandler(),
        InitialPrices(),
        interest_fund_tickers=[],
    )


def _process_single_dividend(
    calculator: CapitalGainsCalculator,
    symbol: str,
    date: datetime.date,
    currency: str,
    gross: Decimal,
    withheld: Decimal,
) -> Dividend:
    """Process one dividend and return the resulting Dividend entry."""
    calculator.dividend_list[(symbol, date)] += ForeignCurrencyAmount(gross, currency)
    calculator.dividend_tax_list[(symbol, date)] += ForeignCurrencyAmount(
        withheld, currency
    )

    calculator.process_dividends()

    entries = calculator.calculation_log_yields[date][f"dividend${symbol}"]
    assert len(entries) == 1
    dividend = entries[0].dividend
    assert dividend is not None
    return dividend


@pytest.mark.parametrize(
    ("symbol", "isin", "gross", "withheld"),
    [
        # Real Fortuneo rows: 15% US tax at source + 12.8% prélèvement fiscal
        # + 17.2% prélèvements sociaux. Withholding far above the treaty rate
        # still credits exactly the treaty rate.
        ("VTRS", "US92556V1061", Decimal("0.61"), Decimal("-0.26")),
        ("PFE", "US7170811035", Decimal("20.07"), Decimal("-9.32")),
    ],
)
def test_eur_dividend_of_us_security_applies_usa_treaty(
    symbol: str, isin: str, gross: Decimal, withheld: Decimal
) -> None:
    """US securities in French custody credit 15% under the USA treaty."""

    date = datetime.date(2026, 6, 18)
    calculator = _make_dividend_calculator(date, "EUR")
    calculator.isin_converter.data[isin] = {symbol}
    calculator.isin_converter.validate_data()

    dividend = _process_single_dividend(
        calculator, symbol, date, "EUR", gross, withheld
    )

    assert dividend.tax_treaty is not None
    # The dividend is US-source (SA106 country line), even via a French bank.
    assert dividend.tax_treaty.country == "USA"
    # Only the 15% treaty rate is creditable against UK tax.
    assert dividend.tax_treaty_amount == gross * Decimal("0.15")


def test_dividend_treaty_requires_known_isin() -> None:
    """Without an ISIN the security country, hence the treaty, is unknown."""

    date = datetime.date(2026, 6, 18)
    calculator = _make_dividend_calculator(date, "USD")

    dividend = _process_single_dividend(
        calculator, "UNKNOWN", date, "USD", Decimal("100"), Decimal("-15")
    )

    assert dividend.tax_treaty is None


def test_dividend_treaty_missing_for_unconfigured_country() -> None:
    """A French security must not get a credit while FR is not configured."""

    date = datetime.date(2026, 6, 18)
    calculator = _make_dividend_calculator(date, "USD")
    # TotalEnergies: French security, USD dividends at a US broker.
    calculator.isin_converter.data["FR0000120271"] = {"TTE"}
    calculator.isin_converter.validate_data()

    dividend = _process_single_dividend(
        calculator, "TTE", date, "USD", Decimal("100"), Decimal("-12.80")
    )

    assert dividend.tax_treaty is None


def test_dividend_treaty_credit_denied_when_under_withheld() -> None:
    """No credit when less than the treaty rate was actually withheld."""

    date = datetime.date(2026, 6, 18)
    calculator = _make_dividend_calculator(date, "USD")
    calculator.isin_converter.data["US7170811035"] = {"PFE"}
    calculator.isin_converter.validate_data()

    # Only 5% withheld: crediting the 15% treaty rate would claim relief
    # for tax that was never paid.
    dividend = _process_single_dividend(
        calculator, "PFE", date, "USD", Decimal("100"), Decimal("-5")
    )

    assert dividend.tax_treaty is None


@pytest.mark.parametrize(
    (
        "tax_year",
        "broker_transactions",
        "expected",
        "expected_unrealized",
        "gbp_prices",
        "current_prices",
        "expected_uk_interest",
        "expected_foreign_interest",
        "expected_dividend",
        "expected_dividend_gain",
        "calculation_log",
        "calculation_log_yields",
    ),
    calc_basic_data + calc_basic_data_2,
)
def test_basic(
    tax_year: int,
    broker_transactions: list[BrokerTransaction],
    expected: float,
    expected_unrealized: float | None,
    gbp_prices: dict[datetime.date, dict[str, Decimal]] | None,
    current_prices: dict[str, Decimal | None] | None,
    expected_uk_interest: float,
    expected_foreign_interest: float,
    expected_dividend: float,
    expected_dividend_gain: float,
    calculation_log: CalculationLog | None,
    calculation_log_yields: CalculationLog | None,
) -> None:
    """Generate basic tests for test data."""
    if gbp_prices is None:
        gbp_prices = {t.date: {"USD": Decimal(1)} for t in broker_transactions}
    currency_converter = CurrencyConverter(None, gbp_prices)
    isin_converter = IsinConverter()
    historical_prices = {
        "FOO": {datetime.date(day=5, month=7, year=2023): Decimal(90)},
        "BAR": {datetime.date(day=5, month=7, year=2023): Decimal(12)},
    }
    price_fetcher = CurrentPriceFetcher(
        currency_converter, current_prices, historical_prices
    )
    spin_off_handler = SpinOffHandler()
    spin_off_handler.cache = {"BAR": "FOO"}
    initial_prices = InitialPrices()
    calculator = CapitalGainsCalculator(
        tax_year,
        currency_converter,
        isin_converter,
        price_fetcher,
        spin_off_handler,
        initial_prices,
        interest_fund_tickers=["FOO"],
        calc_unrealized_gains=expected_unrealized is not None,
    )
    report = get_report(calculator, broker_transactions)
    assert report.total_gain() == round_decimal(Decimal(expected), 2)
    print(str(report))
    if expected_unrealized is not None:
        assert report.total_unrealized_gains() == round_decimal(
            Decimal(expected_unrealized), 2
        )
    assert round_decimal(report.total_uk_interest, 2) == round_decimal(
        Decimal(expected_uk_interest), 2
    )
    assert round_decimal(report.total_foreign_interest, 2) == round_decimal(
        Decimal(expected_foreign_interest), 2
    )
    assert round_decimal(report.total_dividends_amount(), 2) == round_decimal(
        Decimal(expected_dividend), 2
    )
    assert round_decimal(report.total_dividend_taxable_gain(), 2) == round_decimal(
        Decimal(expected_dividend_gain), 2
    )
    if calculation_log is not None:
        result_log = report.calculation_log
        assert len(result_log) == len(calculation_log), (
            f"Actual:\n{result_log}\n\nExpected:\n{calculation_log}\n\n"
        )
        for date_index, expected_entries_map in calculation_log.items():
            assert date_index in result_log
            result_entries_map = result_log[date_index]
            print(date_index)
            print(result_entries_map)
            assert len(result_entries_map) == len(expected_entries_map)
            for entries_type, expected_entries_list in expected_entries_map.items():
                assert entries_type in result_entries_map
                result_entries_list = result_entries_map[entries_type]
                assert len(result_entries_list) == len(expected_entries_list)
                for i, expected_entry in enumerate(expected_entries_list):
                    result_entry = result_entries_list[i]
                    assert result_entry.rule_type == expected_entry.rule_type
                    assert result_entry.quantity == expected_entry.quantity
                    assert result_entry.new_quantity == expected_entry.new_quantity
                    assert round_decimal(
                        result_entry.new_pool_cost, 4
                    ) == round_decimal(expected_entry.new_pool_cost, 4)
                    assert round_decimal(result_entry.gain, 4) == round_decimal(
                        expected_entry.gain, 4
                    )
                    assert round_decimal(result_entry.amount, 4) == round_decimal(
                        expected_entry.amount, 4
                    )
                    assert round_decimal(
                        result_entry.allowable_cost, 4
                    ) == round_decimal(expected_entry.allowable_cost, 4)
                    assert (
                        result_entry.bed_and_breakfast_date_index
                        == expected_entry.bed_and_breakfast_date_index
                    )
                    assert round_decimal(result_entry.fees, 4) == round_decimal(
                        expected_entry.fees, 4
                    )

    if calculation_log_yields is not None:
        result_log = report.calculation_log_yields
        assert len(result_log) == len(calculation_log_yields)
        for date_index, expected_entries_map in calculation_log_yields.items():
            assert date_index in result_log
            result_entries_map = result_log[date_index]
            print(date_index)
            print(result_entries_map)
            assert len(result_entries_map) == len(expected_entries_map)
            for entries_type, expected_entries_list in expected_entries_map.items():
                assert entries_type in result_entries_map
                result_entries_list = result_entries_map[entries_type]
                assert len(result_entries_list) == len(expected_entries_list)
                for i, expected_entry in enumerate(expected_entries_list):
                    result_entry = result_entries_list[i]
                    assert result_entry.rule_type == expected_entry.rule_type
                    assert round_decimal(result_entry.amount, 4) == round_decimal(
                        expected_entry.amount, 4
                    )


def test_bed_and_breakfast_zero_available_quantity_skip() -> None:
    """Later acquisitions are ignored if the disposal was already satisfied."""

    currency_converter = CurrencyConverter(None, {})
    price_fetcher = CurrentPriceFetcher(currency_converter, {}, {})
    calculator = CapitalGainsCalculator(
        2024,
        currency_converter,
        IsinConverter(),
        price_fetcher,
        SpinOffHandler(),
        InitialPrices(),
        interest_fund_tickers=[],
    )

    symbol = "TEST"
    transactions: list[BrokerTransaction] = [
        BrokerTransaction(
            date=datetime.date(2024, 1, 1),
            action=ActionType.TRANSFER,
            symbol=None,
            description="deposit",
            quantity=None,
            price=None,
            fees=Decimal(0),
            amount=Decimal(500),
            currency="GBP",
            broker="Test",
        ),
        BrokerTransaction(
            date=datetime.date(2024, 1, 10),
            action=ActionType.BUY,
            symbol=symbol,
            description="initial buy",
            quantity=Decimal(10),
            price=Decimal(10),
            fees=Decimal(0),
            amount=Decimal(-100),
            currency="GBP",
            broker="Test",
        ),
        BrokerTransaction(
            date=datetime.date(2024, 3, 1),
            action=ActionType.SELL,
            symbol=symbol,
            description="disposal",
            quantity=Decimal(5),
            price=Decimal(12),
            fees=Decimal(0),
            amount=Decimal(60),
            currency="GBP",
            broker="Test",
        ),
        BrokerTransaction(
            date=datetime.date(2024, 3, 5),
            action=ActionType.BUY,
            symbol=symbol,
            description="bed and breakfast buy",
            quantity=Decimal(5),
            price=Decimal(11),
            fees=Decimal(0),
            amount=Decimal(-55),
            currency="GBP",
            broker="Test",
        ),
        BrokerTransaction(
            date=datetime.date(2024, 3, 10),
            action=ActionType.BUY,
            symbol=symbol,
            description="unrelated buy",
            quantity=Decimal(3),
            price=Decimal(9),
            fees=Decimal(0),
            amount=Decimal(-27),
            currency="GBP",
            broker="Test",
        ),
    ]

    report = get_report(calculator, transactions)

    # The original disposal is fully matched against the 5-share buy, so no gain.
    assert report.total_gain() == Decimal(0)

    first_match = datetime.date(2024, 3, 5)
    assert calculator.bnb_list[first_match][symbol].quantity == Decimal(5)

    second_match = datetime.date(2024, 3, 10)
    assert symbol not in calculator.bnb_list.get(second_match, {})


def test_crypto_disposals_are_split_from_listed_securities() -> None:
    """SA108 totals should separate cryptoassets from listed securities."""

    currency_converter = CurrencyConverter(None, {})
    price_fetcher = CurrentPriceFetcher(currency_converter, {}, {})
    calculator = CapitalGainsCalculator(
        2024,
        currency_converter,
        IsinConverter(),
        price_fetcher,
        SpinOffHandler(),
        InitialPrices(),
        interest_fund_tickers=[],
    )

    def gbp_transaction(
        date: datetime.date,
        action: ActionType,
        symbol: str | None,
        quantity: Decimal | None,
        price: Decimal | None,
        amount: Decimal,
    ) -> BrokerTransaction:
        return BrokerTransaction(
            date=date,
            action=action,
            symbol=symbol,
            description=f"{action} {symbol}",
            quantity=quantity,
            price=price,
            fees=Decimal(0),
            amount=amount,
            currency="GBP",
            broker="Test",
        )

    transactions = [
        gbp_transaction(
            datetime.date(2024, 4, 10),
            ActionType.TRANSFER,
            None,
            None,
            None,
            Decimal(10000),
        ),
        # ETH is a cryptoasset by default; FOO is a listed security.
        gbp_transaction(
            datetime.date(2024, 5, 1),
            ActionType.BUY,
            "ETH",
            Decimal(1),
            Decimal(1000),
            Decimal(-1000),
        ),
        gbp_transaction(
            datetime.date(2024, 5, 1),
            ActionType.BUY,
            "FOO",
            Decimal(10),
            Decimal(100),
            Decimal(-1000),
        ),
        gbp_transaction(
            datetime.date(2024, 6, 1),
            ActionType.SELL,
            "ETH",
            Decimal(1),
            Decimal(1500),
            Decimal(1500),
        ),
        gbp_transaction(
            datetime.date(2024, 6, 1),
            ActionType.SELL,
            "FOO",
            Decimal(10),
            Decimal(120),
            Decimal(1200),
        ),
    ]

    report = get_report(calculator, transactions)

    assert report.disposal_count == 2
    assert report.crypto_totals.disposal_count == 1
    assert report.crypto_totals.disposal_proceeds == Decimal(1500)
    assert report.crypto_totals.allowable_costs == Decimal(1000)
    assert report.crypto_totals.capital_gain == Decimal(500)
    assert report.crypto_totals.capital_loss == Decimal(0)

    listed = report.listed_totals
    assert listed.disposal_count == 1
    assert listed.disposal_proceeds == Decimal(1200)
    assert listed.allowable_costs == Decimal(1000)
    assert listed.capital_gain == Decimal(200)
    assert listed.capital_loss == Decimal(0)

    assert "Cryptoassets" in str(report)


def test_run_with_example_files() -> None:
    """Runs the script and verifies it doesn't fail."""
    cmd = build_cmd(
        "--year",
        "2020",
        "--schwab-file",
        "tests/schwab/data/schwab_transactions.csv",
        "--trading212-dir",
        "tests/trading212/data/2020/",
        "--mssb-dir",
        "tests/morgan_stanley/data/",
    )
    result = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if result.returncode:
        pytest.fail(
            "Integration test failed\n"
            f"stdout:\n{result.stdout}\n"
            f"stderr:\n{result.stderr}"
        )

    stderr_lines = result.stderr.strip().split("\n")
    expected_lines = 5
    assert len(stderr_lines) == expected_lines
    assert stderr_lines[0] == "WARNING: No Schwab Award file provided"
    assert stderr_lines[1] == "WARNING: No Schwab transaction file provided"
    assert stderr_lines[2] == "WARNING: No remittance basis file provided"
    assert stderr_lines[3] == "WARNING: No OWR file provided"
    assert stderr_lines[4].startswith("WARNING: Bed and breakfasting for VUAG"), (
        "Unexpected stderr message"
    )
    expected_file = (
        Path("tests") / "general" / "data" / "test_run_with_example_files_output.txt"
    )
    expected = expected_file.read_text(encoding="utf-8")
    cmd_str = " ".join([param if param else "''" for param in cmd])
    assert result.stdout == expected, (
        "Run with example files generated unexpected outputs, "
        "if you added new features update the test with:\n"
        f"{cmd_str} > {expected_file}"
    )
