"""Fortuneo parser."""

from __future__ import annotations

import csv
import datetime
from decimal import Decimal, InvalidOperation
from enum import StrEnum
import logging
from typing import TYPE_CHECKING, Final

from cgt_calc.exceptions import ParsingError
from cgt_calc.model import ActionType, BrokerTransaction

if TYPE_CHECKING:
    from pathlib import Path


BROKER_NAME: Final = "Fortuneo"
LOGGER = logging.getLogger(__name__)


class FortuneoColumn(StrEnum):
    """Columns available in Fortuneo CSV exports."""

    LABEL = "libellé"
    OPERATION = "Opération"
    PLACE = "Place"
    DATE = "Date"
    QUANTITY = "Qté"
    PRICE = "Prix d'éxé"
    GROSS_AMOUNT = "Montant brut"
    WITHHOLDING = "Courtage/Prélèvement"
    NET_AMOUNT = "Montant net"
    CURRENCY = "Devise"


COLUMNS: Final[list[str]] = [column.value for column in FortuneoColumn]
# The only operation translated into transactions. Everything else is skipped,
# notably "OST de création de coupons - Détachement coupon optionnel" which is
# just a notification that a coupon will be paid, not a cash movement.
DIVIDEND_OPERATION: Final = "Encaissement coupons intérêt/dividende"
# Fortuneo CSV exports only carry free-text labels; map them to
# (ticker, ISIN). The ISIN drives the double taxation treaty selection.
FORTUNEO_LABEL_TO_SECURITY: Final[dict[str, tuple[str, str]]] = {
    "Pfizer Inc": ("PFE", "US7170811035"),
    "Viatris": ("VTRS", "US92556V1061"),
}


def _strip_trailing_empty_cells(row: list[str]) -> list[str]:
    """Remove trailing empty cells caused by the final separator."""

    trimmed = list(row)
    while trimmed and trimmed[-1] == "":
        trimmed.pop()
    return trimmed


def _parse_decimal(value: str, *, field_name: str, file: Path) -> Decimal:
    """Parse a decimal value supporting both French and dot decimals."""

    normalized = value.strip().replace(" ", "")
    if not normalized:
        raise ParsingError(file, f"Missing decimal in column '{field_name}'")
    if "," in normalized and "." not in normalized:
        normalized = normalized.replace(",", ".")
    else:
        normalized = normalized.replace(",", "")
    try:
        return Decimal(normalized)
    except InvalidOperation as err:
        raise ParsingError(
            file,
            f"Invalid decimal in column '{field_name}': {value!r}",
        ) from err


def _parse_date(
    value: str, *, file: Path, row_dict: dict[str, str]
) -> datetime.date:
    """Parse a Fortuneo date."""

    try:
        return datetime.datetime.strptime(value.strip(), "%d/%m/%Y").date()
    except ValueError as err:
        raise ParsingError(
            file,
            f"Invalid date format: {value} from row: {row_dict}",
        ) from err


def _get_security(label: str, *, file: Path) -> tuple[str, str]:
    """Translate a Fortuneo security label to a (ticker, ISIN) pair."""

    try:
        return FORTUNEO_LABEL_TO_SECURITY[label.strip()]
    except KeyError as err:
        raise ParsingError(
            file,
            f"No Fortuneo ticker mapping for label {label!r}",
        ) from err


def _validate_header(header: list[str], file: Path) -> None:
    """Validate the Fortuneo header."""

    normalized = [value.strip() for value in header if value.strip()]
    missing = [column for column in COLUMNS if column not in normalized]
    if missing:
        raise ParsingError(file, f"Missing columns: {', '.join(missing)}")


def _row_to_dict(header: list[str], row: list[str]) -> dict[str, str]:
    """Convert a Fortuneo CSV row to a dict keyed by column name."""

    return {
        key.strip(): value.strip()
        for key, value in zip(header, row, strict=True)
        if key.strip()
    }


def _read_csv_rows(transactions_file: Path) -> list[list[str]]:
    """Read a Fortuneo CSV, trying the encodings Fortuneo typically emits."""

    encodings = ("utf-8-sig", "cp1252")
    last_error: UnicodeDecodeError | None = None
    for encoding in encodings:
        try:
            with transactions_file.open(encoding=encoding, newline="") as file:
                LOGGER.info("Parsing %s with %s...", transactions_file, encoding)
                return list(csv.reader(file, delimiter=";"))
        except UnicodeDecodeError as err:
            last_error = err
    assert last_error is not None
    raise ParsingError(
        transactions_file,
        "Unable to decode Fortuneo CSV as UTF-8 or CP1252",
    ) from last_error


def read_fortuneo_transactions(transactions_file: Path) -> list[BrokerTransaction]:
    """Parse Fortuneo dividend transactions from a CSV file."""
    lines = _read_csv_rows(transactions_file)

    if not lines:
        raise ParsingError(transactions_file, "Fortuneo CSV file is empty")

    header = _strip_trailing_empty_cells(lines[0])
    _validate_header(header, transactions_file)

    transactions: list[BrokerTransaction] = []
    for index, raw_row in enumerate(lines[1:], start=2):
        if not any(raw_row):
            continue
        row = _strip_trailing_empty_cells(raw_row)
        try:
            row_dict = _row_to_dict(header, row)
            operation = row_dict[FortuneoColumn.OPERATION.value]
            if operation != DIVIDEND_OPERATION:
                LOGGER.debug("Ignoring Fortuneo operation: %s", operation)
                continue

            date = _parse_date(
                row_dict[FortuneoColumn.DATE.value],
                file=transactions_file,
                row_dict=row_dict,
            )
            symbol, isin = _get_security(
                row_dict[FortuneoColumn.LABEL.value],
                file=transactions_file,
            )
            quantity = _parse_decimal(
                row_dict[FortuneoColumn.QUANTITY.value],
                field_name=FortuneoColumn.QUANTITY.value,
                file=transactions_file,
            )
            gross_amount = _parse_decimal(
                row_dict[FortuneoColumn.GROSS_AMOUNT.value],
                field_name=FortuneoColumn.GROSS_AMOUNT.value,
                file=transactions_file,
            )
            withholding = _parse_decimal(
                row_dict[FortuneoColumn.WITHHOLDING.value],
                field_name=FortuneoColumn.WITHHOLDING.value,
                file=transactions_file,
            )
            # The "Devise" column only logs the currency the security trades
            # in; all monetary amounts in the export are denominated in the
            # account currency, which is always EUR for Fortuneo.
            currency = "EUR"

            transactions.append(
                BrokerTransaction(
                    date=date,
                    action=ActionType.DIVIDEND,
                    symbol=symbol,
                    description=operation,
                    quantity=quantity,
                    price=Decimal(0),
                    fees=Decimal(0),
                    amount=gross_amount,
                    currency=currency,
                    broker=BROKER_NAME,
                    isin=isin,
                )
            )
            if withholding:
                transactions.append(
                    BrokerTransaction(
                        date=date,
                        action=ActionType.NRA_TAX_ADJ,
                        symbol=symbol,
                        description=operation,
                        quantity=quantity,
                        price=Decimal(0),
                        fees=Decimal(0),
                        amount=withholding if withholding < 0 else -withholding,
                        currency=currency,
                        broker=BROKER_NAME,
                        isin=isin,
                    )
                )
        except ParsingError as err:
            err.add_row_context(index)
            raise
        except ValueError as err:
            raise ParsingError(
                transactions_file,
                str(err),
                row_index=index,
            ) from err

    if not transactions:
        LOGGER.warning(
            "No Fortuneo transactions detected in file %s", transactions_file
        )
    return transactions
