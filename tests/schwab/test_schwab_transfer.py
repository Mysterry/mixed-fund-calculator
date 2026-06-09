"""Test Schwab transfer annotation builder."""

from __future__ import annotations

import csv
from pathlib import Path

from cgt_calc.schwab_transfer import build_transfer_file


def _write_csv(path: Path, rows: list[list[str]]) -> None:
    """Write a small CSV file."""

    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerows(rows)


def _read_csv(path: Path) -> list[list[str]]:
    """Read a CSV file."""

    with path.open(encoding="utf-8-sig", newline="") as handle:
        return list(csv.reader(handle))


def test_build_transfer_file_reuses_existing_and_prompts_for_missing(
    tmp_path: Path,
) -> None:
    """Existing annotations should be reused and missing ones prompted."""

    transactions = tmp_path / "transactions.csv"
    existing = tmp_path / "existing_transfers.csv"
    output = tmp_path / "output_transfers.csv"

    _write_csv(
        transactions,
        [
            [
                "Date",
                "Action",
                "Symbol",
                "Description",
                "Quantity",
                "Price",
                "Fees & Comm",
                "Amount",
            ],
            ["05/05/2026", "MoneyLink Transfer", "", "Tfr BANK", "", "", "", "-10.00"],
            ["05/04/2026", "Wire Received", "", "FOREIGN CURRENCY DEPOSIT", "", "", "", "2619.06"],
            ["05/03/2026", "Buy", "META", "META PLATFORMS INC CLASS A", "1", "10", "0", "-10"],
        ],
    )
    _write_csv(
        existing,
        [
            [
                "Date",
                "Action",
                "Description",
                "Amount",
                "Destination (transfer out)",
                "Origin (transfer in)",
            ],
            ["5/5/2026", "MoneyLink Transfer", "Tfr BANK", "-10.00", "UK", ""],
        ],
    )

    prompts: list[str] = []

    def prompt_fn(prompt: str) -> str:
        prompts.append(prompt)
        return "1"

    summary = build_transfer_file(
        transactions_file=transactions,
        existing_transfers_file=existing,
        output_file=output,
        prompt_fn=prompt_fn,
    )

    assert summary.annotated_count == 2
    assert summary.existing_count == 1
    assert len(prompts) == 1

    rows = _read_csv(output)
    assert rows[0] == [
        "Date",
        "Action",
        "Description",
        "Amount",
        "Destination (transfer out)",
        "Origin (transfer in)",
    ]
    assert rows[1] == ["5/5/2026", "MoneyLink Transfer", "Tfr BANK", "-10.00", "UK", ""]
    assert rows[2] == [
        "5/4/2026",
        "Wire Received",
        "FOREIGN CURRENCY DEPOSIT",
        "2619.06",
        "",
        "UK taxed",
    ]


def test_build_transfer_file_rejects_non_matching_existing_row(tmp_path: Path) -> None:
    """Existing annotations that do not appear in the transaction export should fail."""

    transactions = tmp_path / "transactions.csv"
    existing = tmp_path / "existing_transfers.csv"
    output = tmp_path / "output_transfers.csv"

    _write_csv(
        transactions,
        [
            [
                "Date",
                "Action",
                "Symbol",
                "Description",
                "Quantity",
                "Price",
                "Fees & Comm",
                "Amount",
            ],
            ["05/05/2026", "MoneyLink Transfer", "", "Tfr BANK", "", "", "", "-10.00"],
        ],
    )
    _write_csv(
        existing,
        [
            [
                "Date",
                "Action",
                "Description",
                "Amount",
                "Destination (transfer out)",
                "Origin (transfer in)",
            ],
            ["5/4/2026", "MoneyLink Transfer", "Tfr BANK", "-10.00", "UK", ""],
        ],
    )

    try:
        build_transfer_file(
            transactions_file=transactions,
            existing_transfers_file=existing,
            output_file=output,
            prompt_fn=lambda prompt: "1",
        )
    except ValueError as err:
        assert "does not match the transactions file" in str(err)
    else:
        raise AssertionError("expected the transfer matcher to fail")
