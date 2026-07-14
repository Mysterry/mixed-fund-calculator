"""Tests for Fortuneo parser."""

from __future__ import annotations

from decimal import Decimal
from pathlib import Path

import pytest

from cgt_calc.exceptions import ParsingError
from cgt_calc.model import ActionType
from cgt_calc.parsers.fortuneo import read_fortuneo_transactions


def test_read_fortuneo_transactions_parses_dividends_and_ignores_booking(
    tmp_path: Path,
) -> None:
    """Fortuneo dividend rows produce dividend and tax transactions."""

    file_path = tmp_path / "fortuneo.csv"
    file_path.write_text(
        (
            "libellé;Opération;Place;Date;Qté;Prix d'éxé;Montant brut;"
            "Courtage/Prélèvement;Montant net;Devise;\n"
            "Viatris;Encaissement coupons intérêt/dividende;NASDAQ;18/03/2026;6.0;"
            "0.0;0.61;-0.26;0.35;USD;\n"
            "Viatris;OST de création de coupons - Détachement coupon optionnel;"
            "NASDAQ;09/03/2026;6.0;0.0;0.61;0.0;0.61;USD;\n"
        ),
        encoding="utf-8",
    )

    transactions = read_fortuneo_transactions(file_path)

    assert len(transactions) == 2
    dividend, tax = transactions
    assert dividend.action is ActionType.DIVIDEND
    assert dividend.symbol == "VTRS"
    assert dividend.isin == "US92556V1061"
    assert dividend.quantity == Decimal("6.0")
    assert dividend.amount == Decimal("0.61")
    assert dividend.currency == "EUR"

    assert tax.action is ActionType.NRA_TAX_ADJ
    assert tax.symbol == "VTRS"
    assert tax.isin == "US92556V1061"
    assert tax.quantity == Decimal("6.0")
    assert tax.amount == Decimal("-0.26")
    assert tax.currency == "EUR"


def test_read_fortuneo_transactions_accepts_cp1252_encoded_csv(
    tmp_path: Path,
) -> None:
    """Fortuneo files encoded as CP1252 are still readable."""

    file_path = tmp_path / "fortuneo_cp1252.csv"
    file_path.write_bytes(
        (
            "libellé;Opération;Place;Date;Qté;Prix d'éxé;Montant brut;"
            "Courtage/Prélèvement;Montant net;Devise;\n"
            "Viatris;Encaissement coupons intérêt/dividende;NASDAQ;18/03/2026;6.0;"
            "0.0;0.61;-0.26;0.35;USD;\n"
        ).encode("cp1252")
    )

    transactions = read_fortuneo_transactions(file_path)

    assert len(transactions) == 2
    assert transactions[0].symbol == "VTRS"
    assert all(transaction.currency == "EUR" for transaction in transactions)


def test_read_fortuneo_transactions_rejects_unmapped_dividend_label(
    tmp_path: Path,
) -> None:
    """Fortuneo labels must be mapped to real tickers before parsing succeeds."""

    file_path = tmp_path / "fortuneo_unknown.csv"
    file_path.write_text(
        (
            "libellé;Opération;Place;Date;Qté;Prix d'éxé;Montant brut;"
            "Courtage/Prélèvement;Montant net;Devise;\n"
            "Unknown SA;Encaissement coupons intérêt/dividende;EURONEXT;18/03/2026;6.0;"
            "0.0;0.61;-0.26;0.35;EUR;\n"
        ),
        encoding="utf-8",
    )

    with pytest.raises(ParsingError, match="No Fortuneo ticker mapping"):
        read_fortuneo_transactions(file_path)
