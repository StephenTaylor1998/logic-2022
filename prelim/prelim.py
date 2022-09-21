# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: code/prelim/prelim.py

"""Simple module for checking your Python and logic environment."""

from __future__ import annotations

from logic_utils import *

def half(x: int) -> int:
    """Halves the given even integer.

    Parameters:
        x: even integer to halve.

    Returns:
        An integer `z` such that `z`\ ``+``\ `z`\ ``=``\ `x`.
    """
    assert x % 2 == 0
    # Task 0.1
