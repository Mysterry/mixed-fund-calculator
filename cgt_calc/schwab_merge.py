"""Concatenate overlapping Schwab exports after validating headers."""

from __future__ import annotations

import argparse
import csv
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Sequence


@dataclass(frozen=True)
class MergeSummary:
    """Summarize a merge operation."""

    input_files: tuple[Path, ...]
    output_file: Path
    row_count: int


def _flatten_path_groups(path_groups: list[list[Path]]) -> list[Path]:
    """Flatten parsed CLI path groups."""

    return [path for group in path_groups for path in group]


def _read_csv_file(path: Path) -> tuple[list[str], list[list[str]]]:
    """Read a CSV file into header and data rows."""

    with path.open(encoding="utf-8-sig", newline="") as handle:
        rows = list(csv.reader(handle))

    if not rows:
        raise ValueError(f"{path} is empty")

    header = rows[0]
    data_rows = [row for row in rows[1:] if any(row)]
    return header, data_rows


def _merge_csv_files(paths: Sequence[Path]) -> tuple[list[str], list[list[str]]]:
    """Concatenate CSV rows after verifying that all headers match exactly."""

    if not paths:
        raise ValueError("provide at least one input file")

    merged_header: list[str] | None = None
    merged_rows: list[list[str]] = []

    for path in paths:
        header, rows = _read_csv_file(path)
        if merged_header is None:
            merged_header = header
        elif header != merged_header:
            raise ValueError(
                f"header mismatch for {path.name}: expected {merged_header}, got {header}"
            )
        merged_rows.extend(rows)

    assert merged_header is not None
    return merged_header, merged_rows


def _write_csv_file(path: Path, header: Sequence[str], rows: Sequence[Sequence[str]]) -> None:
    """Write a CSV file."""

    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(list(header))
        writer.writerows(rows)


def merge_schwab_exports(
    *,
    transaction_files: Sequence[Path] | None = None,
    transaction_output: Path | None = None,
    award_files: Sequence[Path] | None = None,
    award_output: Path | None = None,
) -> list[MergeSummary]:
    """Merge any provided Schwab CSV groups by concatenation."""

    summaries: list[MergeSummary] = []

    if transaction_files:
        if transaction_output is None:
            raise ValueError("transaction_output is required when transaction_files are provided")
        header, rows = _merge_csv_files(transaction_files)
        _write_csv_file(transaction_output, header, rows)
        summaries.append(
            MergeSummary(
                input_files=tuple(transaction_files),
                output_file=transaction_output,
                row_count=len(rows),
            )
        )

    if award_files:
        if award_output is None:
            raise ValueError("award_output is required when award_files are provided")
        header, rows = _merge_csv_files(award_files)
        _write_csv_file(award_output, header, rows)
        summaries.append(
            MergeSummary(
                input_files=tuple(award_files),
                output_file=award_output,
                row_count=len(rows),
            )
        )

    if not summaries:
        raise ValueError("provide at least one Schwab export group to merge")

    return summaries


def build_parser() -> argparse.ArgumentParser:
    """Build the Schwab merge CLI parser."""

    parser = argparse.ArgumentParser(
        description="Concatenate Charles Schwab CSV exports after validating headers.",
        allow_abbrev=False,
    )
    parser.add_argument(
        "--transactions-in",
        dest="transaction_files",
        action="append",
        nargs="+",
        type=Path,
        default=[],
        metavar="PATH",
        help="one or more Schwab transaction CSV files to concatenate",
    )
    parser.add_argument(
        "--transactions-out",
        type=Path,
        default=None,
        metavar="PATH",
        help="destination for the concatenated Schwab transaction CSV",
    )
    parser.add_argument(
        "--awards-in",
        dest="award_files",
        action="append",
        nargs="+",
        type=Path,
        default=[],
        metavar="PATH",
        help="one or more Schwab award CSV files to concatenate",
    )
    parser.add_argument(
        "--awards-out",
        type=Path,
        default=None,
        metavar="PATH",
        help="destination for the concatenated Schwab award CSV",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    """CLI entry point."""

    parser = build_parser()
    args = parser.parse_args(argv)

    transaction_files = _flatten_path_groups(args.transaction_files)
    award_files = _flatten_path_groups(args.award_files)

    try:
        summaries = merge_schwab_exports(
            transaction_files=transaction_files or None,
            transaction_output=args.transactions_out,
            award_files=award_files or None,
            award_output=args.awards_out,
        )
    except Exception as err:
        parser.error(str(err))
        return 1

    for summary in summaries:
        print(
            f"Combined {len(summary.input_files)} file(s) into {summary.output_file} "
            f"({summary.row_count} data rows)"
        )

    return 0


if __name__ == "__main__":
    sys.exit(main())
