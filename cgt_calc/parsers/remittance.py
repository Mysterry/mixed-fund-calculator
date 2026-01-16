"""Remittance basis files parser."""

from __future__ import annotations

from collections import OrderedDict, defaultdict
import csv
from dataclasses import dataclass
import datetime
from decimal import Decimal
from enum import Enum
import logging
from typing import TYPE_CHECKING, Final

from cgt_calc.const import INTERNAL_START_DATE
from cgt_calc.exceptions import (
    ParsingError,
    SymbolMissingError,
    UnexpectedColumnCountError,
    UnexpectedRowCountError,
)

if TYPE_CHECKING:
    from pathlib import Path

LOGGER = logging.getLogger(__name__)


class RemittanceBasisFileRequiredHeaders(str, Enum):
    """Enum to list the headers in remittance basis file that we will use."""

    TAX_YEAR_STAT = "tax_year_start"
    IS_REMITTANCE_BASIS = "is_remittance_basis"


class OWRFileRequiredHeaders(str, Enum):
    """Enum to list the headers in OWR file that we will use."""

    DATE = "Vest Date"
    BROKER = "Broker"
    SYMBOL = "Symbol"
    QUANTITY = "# of Shares"
    VESTING_DAYS_IN_THREE_YEARS = "Nb days in vesting period in first 3 tax years"
    VESTING_DAYS = "Nb days in vesting period"
    WORKING_DAYS = "Nb working days"
    OVERSEAS_WORKING_DAYS = "Nb overseas working days"


class TaxFilingBasis(Enum):
    """HMRC tax filings possible basis"""

    ARISING = 0
    REMITTANCE = 1


class Destination(Enum):
    OVERSEAS = 0
    UK = 1


class Origin(Enum):
    NON_UK_TAXED = 0
    UK_TAXED = 1


@dataclass
class TaxFilings:
    """Class representing a history of tax filing basis choices per tax year (arising or remittance basis)"""

    tax_filings: OrderedDict[int, TaxFilingBasis]

    def __init__(self,
                 tax_filings: OrderedDict[int, int],
                 file
    ):
        self.tax_filings = OrderedDict()
        for year, is_remittance_basis in tax_filings.items():
            if type(year) != int:
                raise ParsingError(file, f"Years should be integers: {year}")
            if year < INTERNAL_START_DATE.year:
                raise ParsingError(file, f"Years should be higher than the system internal start date: {year}")
            if is_remittance_basis not in [TaxFilingBasis.REMITTANCE.value, TaxFilingBasis.ARISING.value]:
                raise ParsingError(file, f"Is remittance basis needs to be coded with 0 or 1: {is_remittance_basis}")
            self.tax_filings[year] = TaxFilingBasis.REMITTANCE if is_remittance_basis == TaxFilingBasis.REMITTANCE.value else TaxFilingBasis.ARISING

    def get(self, year: int) -> TaxFilingBasis:
        return self.tax_filings[year]


@dataclass
class OWREvent:
    """Class representing an OWR event"""

    date: datetime.date
    broker: str
    symbol: str
    quantity: Decimal
    vesting_days_in_three_years: int
    vesting_days: int
    working_days: int
    overseas_working_days: int

    def __init__(self,
                 row_dict: OrderedDict[str, str],
                 file
    ):

        date_header = OWRFileRequiredHeaders.DATE.value
        date_str = row_dict[date_header]
        try:
            self.date = datetime.datetime.strptime(date_str, "%m/%d/%Y").date()
        except ValueError as exc:
            raise ParsingError(
                file, f"Invalid date format: {date_str} from row: {row_dict}"
            ) from exc
        broker_header = OWRFileRequiredHeaders.BROKER.value
        self.broker = row_dict[broker_header]
        symbol_header = OWRFileRequiredHeaders.SYMBOL.value
        self.symbol = row_dict[symbol_header]
        quantity_header = OWRFileRequiredHeaders.QUANTITY.value
        self.quantity = Decimal(row_dict[quantity_header])
        vesting_days_in_three_years_header = OWRFileRequiredHeaders.VESTING_DAYS_IN_THREE_YEARS.value
        self.vesting_days_in_three_years = int(row_dict[vesting_days_in_three_years_header])
        vesting_days_header = OWRFileRequiredHeaders.VESTING_DAYS.value
        self.vesting_days = int(row_dict[vesting_days_header])
        working_days_header = OWRFileRequiredHeaders.WORKING_DAYS.value
        self.working_days = int(row_dict[working_days_header])
        overseas_working_days_header = OWRFileRequiredHeaders.OVERSEAS_WORKING_DAYS.value
        self.overseas_working_days = int(row_dict[overseas_working_days_header])

def read_remittance_basis(
    remittance_basis_file: Path | None,
) -> TaxFilings:
    """Read remittance basis history from csv file."""
    if remittance_basis_file is None:
        LOGGER.warning("No remittance basis file provided")
        return TaxFilings(tax_filings=OrderedDict(), file=remittance_basis_file)

    with remittance_basis_file.open(encoding="utf-8") as csv_file:
        print(f"Parsing {remittance_basis_file}...")
        lines = list(csv.reader(csv_file))
    if not lines:
        raise ParsingError(
            remittance_basis_file, "Remittance basis file is empty"
        )
    headers = lines[0]
    required_headers = set(
        {header.value for header in RemittanceBasisFileRequiredHeaders}
    )
    if not required_headers.issubset(headers):
        raise ParsingError(
            remittance_basis_file,
            f"Missing columns in remittance basis file: {required_headers.difference(headers)}",
        )

    # Remove headers
    lines = lines[1:]

    tax_filings = OrderedDict(
        {int(row[0]): int(row[1]) for row in lines if any(row)}
    )
    return TaxFilings(tax_filings=tax_filings, file=remittance_basis_file)

def read_owr(
    owr_file: Path | None,
) -> list[OWREvent]:
    """Read OWR events from CSV file."""
    if owr_file is None:
        LOGGER.warning("No OWR file provided")
        return list()
    with owr_file.open(encoding="utf-8") as csv_file:
        print(f"Parsing {owr_file}...")
        lines = list(csv.reader(csv_file))
    if not lines:
        raise ParsingError(
            owr_file, "OWR file is empty"
        )
    headers = lines[0]
    required_headers = set(
        {header.value for header in OWRFileRequiredHeaders}
    )
    if not required_headers.issubset(headers):
        raise ParsingError(
            owr_file,
            f"Missing columns in OWR file: {required_headers.difference(headers)}",
        )

    # Remove headers
    lines = lines[1:]

    owr_events = [
        OrderedDict(zip(headers, row, strict=True))
        for row in lines
        if any(row)
    ]
    return [OWREvent(owr_event, owr_file) for owr_event in owr_events]
