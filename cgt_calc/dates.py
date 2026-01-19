"""Function to work with dates."""

import datetime


def is_date(date: datetime.date) -> bool:
    """Check if date has only date but not time."""
    if not isinstance(date, datetime.date) or isinstance(date, datetime.datetime):
        raise TypeError(f'should be datetime.date: {type(date)} "{date}"')
    return True


def get_tax_year_start(tax_year: int) -> datetime.date:
    """Return tax year start date."""
    # 6 April
    return datetime.date(tax_year, 4, 6)


def get_tax_year_end(tax_year: int) -> datetime.date:
    """Return tax year end date."""
    # 5 April
    return datetime.date(tax_year + 1, 4, 5)

def get_tax_year_index_from_date(date: datetime.date) -> int:
    """ From a date, gives the year corresponding to the start of the tax year the day is in
    e.g. 2024-01-01 is in the 2023/2024 tax year, so returns the int 2023"""

    if date.month > 4 or (date.month == 4 and date.day >= 6):
        return date.year
    else:
        return date.year - 1
