"""Tests for currency converter exchange rate loading."""

from __future__ import annotations

import datetime
from decimal import Decimal
import re
from typing import TYPE_CHECKING

import pytest

from cgt_calc.currency_converter import CurrencyConverter
from cgt_calc.exceptions import ExternalApiError, ParsingError

if TYPE_CHECKING:
    from pathlib import Path


def test_read_exchange_rates_successfully(tmp_path: Path) -> None:
    """Loading a populated rates file captures every row."""
    rates_file = tmp_path / "rates.csv"
    rates_file.write_text(
        "month,currency,rate\n2024-01-01,USD,1.25\n2024-02-01,EUR,1.10\n",
        encoding="utf8",
    )

    converter = CurrencyConverter(exchange_rates_file=rates_file)

    january_rates = converter.cache[datetime.date(2024, 1, 1)]
    february_rates = converter.cache[datetime.date(2024, 2, 1)]
    assert january_rates == {"USD": Decimal("1.25")}
    assert february_rates == {"EUR": Decimal("1.10")}


def test_read_exchange_rates_handles_empty_file(tmp_path: Path) -> None:
    """Empty rates files produce an empty cache without failing."""
    rates_file = tmp_path / "empty.csv"
    # create an empty file
    rates_file.touch()

    converter = CurrencyConverter(exchange_rates_file=rates_file)

    assert converter.cache == {}


def test_read_exchange_rates_skips_blank_rows(tmp_path: Path) -> None:
    """Blank rows are ignored rather than causing parsing errors."""
    rates_file = tmp_path / "blank.csv"
    rates_file.write_text(
        "month,currency,rate\n2024-01-01,USD,1.25\n,,\n2024-02-01,EUR,1.10\n",
        encoding="utf8",
    )

    converter = CurrencyConverter(exchange_rates_file=rates_file)

    january = datetime.date(2024, 1, 1)
    february = datetime.date(2024, 2, 1)
    assert converter.cache[january] == {"USD": Decimal("1.25")}
    assert converter.cache[february] == {"EUR": Decimal("1.10")}


def test_read_exchange_rates_raises_on_invalid_date(tmp_path: Path) -> None:
    """Invalid month values raise a parsing error with context."""
    rates_file = tmp_path / "invalid_date.csv"
    rates_file.write_text(
        "month,currency,rate\n2024/01/01,USD,1.25\n",
        encoding="utf8",
    )

    with pytest.raises(ParsingError, match="Invalid date '2024/01/01'"):
        CurrencyConverter(exchange_rates_file=rates_file)


def test_read_exchange_rates_raises_on_invalid_rate(tmp_path: Path) -> None:
    """Non-decimal rate values raise a parsing error."""
    rates_file = tmp_path / "invalid_rate.csv"
    rates_file.write_text(
        "month,currency,rate\n2024-01-01,USD,one.two\n",
        encoding="utf8",
    )

    with pytest.raises(
        ParsingError,
        match=re.escape("Invalid rate 'one.two'"),
    ):
        CurrencyConverter(exchange_rates_file=rates_file)


def test_read_exchange_rates_raises_on_duplicate_currency(tmp_path: Path) -> None:
    """Duplicate currency entries for the same month raise a parsing error."""
    rates_file = tmp_path / "duplicate.csv"
    rates_file.write_text(
        "month,currency,rate\n2024-01-01,USD,1.25\n2024-01-01,USD,1.30\n",
        encoding="utf8",
    )

    with pytest.raises(
        ParsingError,
        match="Duplicate currency entry for USD on 2024-01-01",
    ):
        CurrencyConverter(exchange_rates_file=rates_file)


def test_currency_rate_falls_back_to_latest_cached_value_on_future_api_failure(
    caplog: pytest.LogCaptureFixture,
) -> None:
    """A failed future-month fetch falls back to the latest cached rate."""
    converter = CurrencyConverter(
        initial_data={
            datetime.date(2026, 6, 1): {"USD": Decimal("1.25")},
            datetime.date(2026, 5, 1): {"USD": Decimal("1.20")},
        }
    )

    def raise_external_error(date: datetime.date) -> None:
        raise ExternalApiError(
            "https://example.invalid",
            "HMRC API returned HTTP 404 for 2027-04.",
        )

    converter._query_hmrc_api = raise_external_error  # type: ignore[method-assign]

    caplog.set_level("WARNING")
    rate = converter.currency_to_gbp_rate("USD", datetime.date(2027, 4, 1))

    assert rate == Decimal("1.25")
    assert "defaulting to the latest cached USD rate as of 2026-06-01" in caplog.text
