"""Build Schwab transfer annotations from a transaction export."""

from __future__ import annotations

from collections import Counter, OrderedDict, defaultdict
import argparse
import csv
import datetime
from dataclasses import dataclass
from decimal import Decimal
import sys
from pathlib import Path
from typing import TYPE_CHECKING, Callable

from .exceptions import ParsingError
from .model import ActionType
from .parsers.schwab import (
    SchwabTransfer,
    SchwabTransfersFileRequiredHeaders,
    SchwabTransactionsFileRequiredHeaders,
    action_from_str,
    format_schwab_date,
    format_schwab_money,
    parse_schwab_date,
    parse_schwab_money,
)
from .parsers.remittance import Destination, Origin

if TYPE_CHECKING:
    from collections.abc import Sequence


@dataclass(frozen=True)
class TransferCandidate:
    """Transaction row that needs transfer annotation."""

    date: datetime.date
    raw_action: str
    description: str
    amount: Decimal
    action: ActionType


@dataclass(frozen=True)
class TransferBuildSummary:
    """Summarize a transfer-annotation build."""

    transaction_file: Path
    output_file: Path
    annotated_count: int
    existing_count: int


def _validate_transaction_headers(headers: list[str], file: Path) -> None:
    """Ensure the Schwab transaction file exposes the expected columns."""

    required_headers = {
        header.value for header in SchwabTransactionsFileRequiredHeaders
    }
    if not required_headers.issubset(headers):
        raise ParsingError(
            file,
            "Missing columns in Schwab transaction file: "
            f"{required_headers.difference(headers)}",
        )


def _read_transfer_candidates(path: Path) -> list[TransferCandidate]:
    """Extract transfer-related rows from a Schwab transaction CSV."""

    with path.open(encoding="utf-8-sig", newline="") as handle:
        rows = list(csv.reader(handle))

    if not rows:
        raise ParsingError(path, "Charles Schwab transactions CSV file is empty")

    headers = rows[0]
    _validate_transaction_headers(headers, path)

    candidates: list[TransferCandidate] = []
    for row in rows[1:]:
        if not any(row):
            continue
        row_dict = OrderedDict(zip(headers, row, strict=True))
        raw_action = row_dict[SchwabTransactionsFileRequiredHeaders.ACTION.value]
        action = action_from_str(raw_action, path)
        if action not in [ActionType.TRANSFER, ActionType.WIRE_FUNDS_RECEIVED]:
            continue

        date = parse_schwab_date(
            row_dict[SchwabTransactionsFileRequiredHeaders.DATE.value], path, row_dict
        )
        description = row_dict[SchwabTransactionsFileRequiredHeaders.DESCRIPTION.value]
        amount = parse_schwab_money(
            row_dict[SchwabTransactionsFileRequiredHeaders.AMOUNT.value], path, row_dict
        )
        if amount is None:
            raise ParsingError(path, f"Missing transfer amount from row: {row_dict}")

        candidates.append(
            TransferCandidate(
                date=date,
                raw_action=raw_action,
                description=description,
                amount=amount,
                action=action,
            )
        )

    return candidates


def _read_existing_transfers(path: Path) -> list[SchwabTransfer]:
    """Read an existing Schwab transfer annotation file."""

    with path.open(encoding="utf-8-sig", newline="") as handle:
        rows = list(csv.reader(handle))

    if not rows:
        raise ParsingError(path, "Charles Schwab transfer CSV file is empty")

    headers = rows[0]
    required_headers = {
        header.value for header in SchwabTransfersFileRequiredHeaders
    }
    if not required_headers.issubset(headers):
        raise ParsingError(
            path,
            "Missing columns in Schwab transfers file: "
            f"{required_headers.difference(headers)}",
        )

    transfers: list[SchwabTransfer] = []
    for row in rows[1:]:
        if not any(row):
            continue
        transfers.append(
            SchwabTransfer.create(OrderedDict(zip(headers, row, strict=True)), path)
        )

    return transfers


def _transfer_key(
    date: datetime.date, raw_action: str, description: str, amount: Decimal
) -> tuple[datetime.date, str, str, Decimal]:
    """Build a stable key for matching transfer rows."""

    return date, raw_action, description, amount


def _existing_transfer_key(
    transfer: SchwabTransfer,
) -> tuple[datetime.date, str, str, Decimal]:
    """Build a stable key for an existing transfer annotation row."""

    assert transfer.amount is not None
    return _transfer_key(
        transfer.date,
        transfer.raw_action,
        transfer.description,
        transfer.amount,
    )


def _prompt_destination(
    candidate: TransferCandidate,
    prompt_fn: Callable[[str], str],
) -> Destination:
    """Prompt for a transfer-out destination."""

    prompt = (
        f"\nTransfer out needs destination\n"
        f"Date: {format_schwab_date(candidate.date)}\n"
        f"Action: {candidate.raw_action}\n"
        f"Description: {candidate.description}\n"
        f"Amount: {format_schwab_money(candidate.amount)}\n"
        "Choose destination [1=UK, 2=Overseas]: "
    )
    while True:
        answer = prompt_fn(prompt).strip().lower()
        if answer in {"1", "uk"}:
            return Destination.UK
        if answer in {"2", "overseas", "o"}:
            return Destination.OVERSEAS
        print("Invalid choice. Enter 1 for UK or 2 for Overseas.")


def _prompt_origin(
    candidate: TransferCandidate,
    prompt_fn: Callable[[str], str],
) -> Origin:
    """Prompt for a transfer-in origin."""

    prompt = (
        f"\nTransfer in needs origin\n"
        f"Date: {format_schwab_date(candidate.date)}\n"
        f"Action: {candidate.raw_action}\n"
        f"Description: {candidate.description}\n"
        f"Amount: {format_schwab_money(candidate.amount)}\n"
        "Choose origin [1=UK taxed, 2=Non UK taxed]: "
    )
    while True:
        answer = prompt_fn(prompt).strip().lower()
        if answer in {"1", "uk taxed", "uk"}:
            return Origin.UK_TAXED
        if answer in {"2", "non uk taxed", "non-uk taxed", "nonuk taxed"}:
            return Origin.NON_UK_TAXED
        print("Invalid choice. Enter 1 for UK taxed or 2 for Non UK taxed.")


def _candidate_to_transfer(
    candidate: TransferCandidate,
    prompt_fn: Callable[[str], str],
) -> SchwabTransfer:
    """Prompt for any missing annotation and build a Schwab transfer row."""

    destination: Destination | None = None
    origin: Origin | None = None

    if candidate.action == ActionType.TRANSFER:
        destination = _prompt_destination(candidate, prompt_fn)
    elif candidate.action == ActionType.WIRE_FUNDS_RECEIVED:
        origin = _prompt_origin(candidate, prompt_fn)
    else:
        raise ParsingError(
            Path("<memory>"),
            f"Unexpected transfer action type: {candidate.action}",
        )

    row = OrderedDict(
        [
            (
                SchwabTransfersFileRequiredHeaders.DATE.value,
                format_schwab_date(candidate.date),
            ),
            (SchwabTransfersFileRequiredHeaders.ACTION.value, candidate.raw_action),
            (
                SchwabTransfersFileRequiredHeaders.DESCRIPTION.value,
                candidate.description,
            ),
            (
                SchwabTransfersFileRequiredHeaders.AMOUNT.value,
                format_schwab_money(candidate.amount),
            ),
            (
                SchwabTransfersFileRequiredHeaders.DESTINATION.value,
                destination.value if destination is not None else "",
            ),
            (
                SchwabTransfersFileRequiredHeaders.ORIGIN.value,
                origin.value if origin is not None else "",
            ),
        ],
    )
    return SchwabTransfer.create(row, Path("<generated>"))


def build_transfer_file(
    *,
    transactions_file: Path,
    output_file: Path,
    existing_transfers_file: Path | None = None,
    prompt_fn: Callable[[str], str] = input,
) -> TransferBuildSummary:
    """Build a Schwab transfer annotation file from transaction rows."""

    candidates = _read_transfer_candidates(transactions_file)
    existing_transfers = (
        _read_existing_transfers(existing_transfers_file)
        if existing_transfers_file is not None
        else []
    )

    candidate_counts = Counter(
        _transfer_key(c.date, c.raw_action, c.description, c.amount)
        for c in candidates
    )
    existing_counts = Counter(_existing_transfer_key(t) for t in existing_transfers)

    for key, count in existing_counts.items():
        if count > candidate_counts[key]:
            date, raw_action, description, amount = key
            raise ValueError(
                "Existing transfer file contains a row that does not match the "
                "transactions file: "
                f"{format_schwab_date(date)} | {raw_action} | {description} | "
                f"{format_schwab_money(amount)}"
            )

    existing_by_key: dict[tuple[datetime.date, str, str, Decimal], list[SchwabTransfer]] = defaultdict(list)
    for transfer in existing_transfers:
        existing_by_key[_existing_transfer_key(transfer)].append(transfer)

    output_rows: list[SchwabTransfer] = []
    for candidate in candidates:
        key = _transfer_key(
            candidate.date, candidate.raw_action, candidate.description, candidate.amount
        )
        if existing_by_key[key]:
            output_rows.append(existing_by_key[key].pop(0))
            continue
        output_rows.append(_candidate_to_transfer(candidate, prompt_fn))

    leftover = [key for key, transfers in existing_by_key.items() if transfers]
    if leftover:
        date, raw_action, description, amount = leftover[0]
        raise ValueError(
            "Existing transfer file contains a row that does not match the "
            "transactions file: "
            f"{format_schwab_date(date)} | {raw_action} | {description} | "
            f"{format_schwab_money(amount)}"
        )

    output_file.parent.mkdir(parents=True, exist_ok=True)
    with output_file.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(
            [header.value for header in SchwabTransfersFileRequiredHeaders]
        )
        for transfer in output_rows:
            assert transfer.amount is not None
            writer.writerow(
                [
                    format_schwab_date(transfer.date),
                    transfer.raw_action,
                    transfer.description,
                    format_schwab_money(transfer.amount),
                    transfer.destination.value if transfer.destination else "",
                    transfer.origin.value if transfer.origin else "",
                ]
            )

    return TransferBuildSummary(
        transaction_file=transactions_file,
        output_file=output_file,
        annotated_count=len(output_rows),
        existing_count=len(existing_transfers),
    )


def build_parser() -> argparse.ArgumentParser:
    """Build the cgt-transfer CLI parser."""

    parser = argparse.ArgumentParser(
        description="Build Schwab transfer annotations from a transaction export.",
        allow_abbrev=False,
    )
    parser.add_argument(
        "--transactions-file",
        type=Path,
        required=True,
        metavar="PATH",
        help="Schwab transaction CSV file",
    )
    parser.add_argument(
        "--existing-transfers-file",
        type=Path,
        default=None,
        metavar="PATH",
        help="optional existing Schwab transfer annotation CSV file",
    )
    parser.add_argument(
        "--output-file",
        type=Path,
        required=True,
        metavar="PATH",
        help="destination for the generated transfer annotation CSV",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    """CLI entry point."""

    parser = build_parser()
    args = parser.parse_args(argv)

    try:
        summary = build_transfer_file(
            transactions_file=args.transactions_file,
            existing_transfers_file=args.existing_transfers_file,
            output_file=args.output_file,
        )
    except Exception as err:
        parser.error(str(err))
        return 1

    print(
        f"Wrote {summary.annotated_count} transfer rows to {summary.output_file} "
        f"({summary.existing_count} existing annotations reused)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
