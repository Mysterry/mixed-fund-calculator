"""Temporary Repatriation Facility (TRF) declaration handler (RDRM70000)."""

from __future__ import annotations

import csv
import decimal
import logging
from dataclasses import dataclass
from decimal import Decimal
from typing import TYPE_CHECKING, Final

from .model import (
    ALREADY_UK_TAXED_CATEGORIES,
    MixedFundMoneyCategory,
    TRF_CAPITAL_TAX_YEAR,
    TRF_RELEVANT_TAX_YEARS,
)

if TYPE_CHECKING:
    from pathlib import Path

LOGGER = logging.getLogger(__name__)

TRF_FILE_HEADERS: Final = [
    "declaration_tax_year",
    "broker",
    "source_tax_year",
    "category",
    "amount",
]

# Sentinel category name stored in the CSV when the user chose not to declare
# for a given (year, broker). Distinguishes "no record yet" (file has no row)
# from "user was asked and declined" (file has a NONE sentinel row).
_DECLINED_SENTINEL: Final = "NONE"


@dataclass
class _TRFRow:
    declaration_tax_year: int
    broker: str
    source_tax_year: int
    category: str
    amount: Decimal


class TRFHandler:
    """Read/write TRF declarations from a CSV file and prompt the user interactively."""

    def __init__(self, trf_file: Path | None, prompt: bool = True):
        self.trf_file = trf_file
        self.prompt = prompt
        self.rows: list[_TRFRow] = self._read_trf_file()

    def _read_trf_file(self) -> list[_TRFRow]:
        if self.trf_file is None or not self.trf_file.is_file():
            return []
        rows: list[_TRFRow] = []
        with self.trf_file.open(encoding="utf-8") as fin:
            reader = csv.DictReader(fin)
            for line in reader:
                if sorted(line.keys()) != sorted(TRF_FILE_HEADERS):
                    from .exceptions import ParsingError
                    raise ParsingError(
                        self.trf_file,
                        f"unexpected columns {sorted(line.keys())}, "
                        f"expected {sorted(TRF_FILE_HEADERS)}",
                    )
                rows.append(
                    _TRFRow(
                        declaration_tax_year=int(line["declaration_tax_year"]),
                        broker=line["broker"],
                        source_tax_year=int(line["source_tax_year"]),
                        category=line["category"],
                        amount=Decimal(line["amount"]),
                    )
                )
        return rows

    def _write_trf_file(self) -> None:
        if self.trf_file is None:
            return
        from .util import open_with_parents
        with open_with_parents(self.trf_file) as fout:
            writer = csv.writer(fout)
            writer.writerow(TRF_FILE_HEADERS)
            for row in self.rows:
                writer.writerow([
                    row.declaration_tax_year,
                    row.broker,
                    row.source_tax_year,
                    row.category,
                    row.amount,
                ])

    def _upsert_rows(
        self,
        year: int,
        broker: str,
        allocations: dict[tuple[int, MixedFundMoneyCategory], Decimal],
    ) -> None:
        """Replace all rows for (year, broker) with new allocations.

        An empty allocations dict is stored as a single NONE sentinel row so
        future runs know the user was already asked and declined.
        """
        self.rows = [
            r for r in self.rows
            if not (r.declaration_tax_year == year and r.broker == broker)
        ]
        if allocations:
            for (source_year, category), amount in allocations.items():
                self.rows.append(_TRFRow(
                    declaration_tax_year=year,
                    broker=broker,
                    source_tax_year=source_year,
                    category=category.name,
                    amount=amount,
                ))
        else:
            self.rows.append(_TRFRow(
                declaration_tax_year=year,
                broker=broker,
                source_tax_year=0,
                category=_DECLINED_SENTINEL,
                amount=Decimal(0),
            ))

    def get_declarations(self, year: int) -> list[_TRFRow]:
        """Return all non-declined TRF rows for a declaration tax year.

        Ordered by broker, then by source year descending / category, matching
        the priority order used by withdraw_money_buckets_order and the
        declaration prompt.
        """
        rows = [r for r in self.rows if r.declaration_tax_year == year and r.category != _DECLINED_SENTINEL]
        return sorted(
            rows,
            key=lambda r: (r.broker, -r.source_tax_year, MixedFundMoneyCategory[r.category].value),
        )

    def get_applicable_allocations(
        self, year: int, broker: str
    ) -> dict[tuple[int, MixedFundMoneyCategory], Decimal] | None:
        """Return recorded allocations for (year, broker).

        Returns None if no record exists at all (user has not been asked yet),
        or an empty dict if the user previously declined.
        """
        matching = [
            r for r in self.rows
            if r.declaration_tax_year == year and r.broker == broker
        ]
        if not matching:
            return None
        return {
            (r.source_tax_year, MixedFundMoneyCategory[r.category]): r.amount
            for r in matching
            if r.category != _DECLINED_SENTINEL
        }

    def declare_for_year(
        self,
        year: int,
        broker: str,
        available_buckets: list[tuple[int, MixedFundMoneyCategory, Decimal]],
        existing: dict[tuple[int, MixedFundMoneyCategory], Decimal] | None,
        tax_filings=None,
    ) -> dict[tuple[int, MixedFundMoneyCategory], Decimal]:
        """Interactively declare (or reuse/overwrite) a TRF declaration.

        Only called for year in TRF_RELEVANT_TAX_YEARS and year == self.tax_year.
        Returns the final allocations dict (possibly empty).
        Pre-2025 arising-basis years are excluded: gains from those years were already
        UK-taxed when they arose, so TRF buys nothing on them.
        """
        def is_eligible(tax_year: int, category: MixedFundMoneyCategory) -> bool:
            return (
                tax_year < 2025
                and category not in ALREADY_UK_TAXED_CATEGORIES
                and (
                    tax_filings is None
                    or (
                        tax_filings.get(tax_year) is not None
                        and tax_filings.get(tax_year).value  # TaxFilingBasis.REMITTANCE.value == 1
                    )
                )
            )

        eligible = [
            (ty, cat, amt) for ty, cat, amt in available_buckets if amt and is_eligible(ty, cat)
        ]

        if not self.prompt:
            return existing or {}

        if existing is not None:
            answer = input(
                f"A TRF declaration for {broker} in tax year {year}/{year + 1} already "
                f"exists. Overwrite? [y/N]: "
            ).strip().lower()
            if answer != "y":
                return existing

        if not eligible:
            return existing or {}

        answer = input(
            f"Do you want to make a TRF declaration for {broker} for tax year "
            f"{year}/{year + 1}? [y/N]: "
        ).strip().lower()
        if answer != "y":
            self._upsert_rows(year, broker, {})
            self._write_trf_file()
            return {}

        print(
            f"All buckets for {broker} "
            f"(balances as of start of {year}/{year + 1}, after any prior TRF declarations):"
        )
        allocations: dict[tuple[int, MixedFundMoneyCategory], Decimal] = {}
        covered_total = Decimal("0")
        # available_buckets already comes in the priority order used by
        # withdraw_money_buckets_order: most recent tax year first, then
        # categories in enum order.
        for tax_year, category, raw_amount in available_buckets:
            amount = raw_amount.quantize(Decimal("0.01"), rounding=decimal.ROUND_DOWN)
            label = (
                "TRF Capital"
                if tax_year == TRF_CAPITAL_TAX_YEAR
                else f"{tax_year}/{tax_year + 1}"
            )
            if not is_eligible(tax_year, category):
                while True:
                    raw = input(
                        f"  {label} {category.name} (£{amount}): not eligible for TRF, "
                        "press Enter to continue: "
                    )
                    if raw.strip() == "":
                        break
                    print("  Not eligible for TRF, just press Enter.")
            else:
                while True:
                    raw = input(
                        f"  {label} {category.name} "
                        f"(available £{amount}, 0 to skip, 'all' for full amount): "
                    ).strip() or "0"
                    if raw.lower() == "all":
                        value = amount
                        break
                    try:
                        value = Decimal(raw).quantize(Decimal("0.01"), rounding=decimal.ROUND_HALF_UP)
                    except (decimal.InvalidOperation, decimal.DecimalException):
                        print("  Not a valid amount.")
                        continue
                    if value < 0 or value > amount:
                        print(f"  Must be between 0 and £{amount}.")
                        continue
                    break
                if value:
                    allocations[(tax_year, category)] = value
            covered_total += amount
            running_total = sum(allocations.values())
            print(
                f"  Running total declared for {broker}: £{running_total} "
                f"(of £{covered_total} covered so far)"
            )

        self._upsert_rows(year, broker, allocations)
        self._write_trf_file()
        return allocations
