# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: code/prelim/prelim_test.py

"""Tests for the prelim.prelim module."""

from prelim.prelim import half

def test_half(debug=False):
    if debug:
        print("Testing half of 42")
    result = half(42)
    assert isinstance(result, int)
    assert result + result == 42

    if debug:
        print("Testing half of 8")
    result = half(8)
    assert isinstance(result, int)
    assert result + result == 8

def test_all(debug=False):
    test_half(debug)
