"""Test Schwab export merger."""

from __future__ import annotations

import csv
from pathlib import Path

from cgt_calc.schwab_merge import merge_schwab_exports


def _read_csv_rows(path: Path) -> list[list[str]]:
    """Read all rows from a CSV file."""

    with path.open(encoding="utf-8-sig", newline="") as handle:
        return list(csv.reader(handle))


def test_merge_schwab_transactions_concatenates_rows(tmp_path: Path) -> None:
    """Transaction files should be concatenated in input order."""

    source = Path("tests/schwab/data/2023/transactions.csv")
    output = tmp_path / "merged_transactions.csv"

    merge_schwab_exports(
        transaction_files=[source, source],
        transaction_output=output,
    )

    source_rows = _read_csv_rows(source)
    merged_rows = _read_csv_rows(output)

    assert merged_rows[0] == source_rows[0]
    assert merged_rows[1:] == source_rows[1:] + source_rows[1:]


def test_merge_schwab_awards_concatenates_rows(tmp_path: Path) -> None:
    """Award files should be concatenated in input order."""

    source = Path("tests/schwab/data/rsu_settlement/awards.csv")
    output = tmp_path / "merged_awards.csv"

    merge_schwab_exports(
        award_files=[source, source],
        award_output=output,
    )

    source_rows = _read_csv_rows(source)
    merged_rows = _read_csv_rows(output)

    assert merged_rows[0] == source_rows[0]
    assert merged_rows[1:] == source_rows[1:] + source_rows[1:]


def test_merge_schwab_rejects_header_mismatch(tmp_path: Path) -> None:
    """Files with different headers should fail fast."""

    left = tmp_path / "left.csv"
    right = tmp_path / "right.csv"
    out = tmp_path / "out.csv"

    left.write_text("A,B\n1,2\n", encoding="utf-8")
    right.write_text("A,C\n3,4\n", encoding="utf-8")

    try:
        merge_schwab_exports(transaction_files=[left, right], transaction_output=out)
    except ValueError as err:
        assert "header mismatch" in str(err)
    else:
        raise AssertionError("expected a header mismatch error")
