"""Test remittance basis parser."""

from __future__ import annotations

from pathlib import Path

from cgt_calc.parsers.remittance import read_owr


def test_read_owr_accepts_iso_dates(tmp_path: Path) -> None:
    """OWR parser should accept YYYY-MM-DD vest dates."""

    owr_file = tmp_path / "owr.csv"
    owr_file.write_text(
        (
            "Vest Date,Broker,Symbol,# of Shares,"
            "Nb days in vesting period in first 3 tax years,"
            "Nb days in vesting period,Nb working days,Nb overseas working days\n"
            "2020-11-15,Charles Schwab,META,42,88,88,60,60\n"
        ),
        encoding="utf-8",
    )

    events = read_owr(owr_file)

    assert len(events) == 1
    assert events[0].date.isoformat() == "2020-11-15"
    assert events[0].broker == "Charles Schwab"
    assert events[0].symbol == "META"
