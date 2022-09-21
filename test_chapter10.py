# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: test_chapter10.py

"""Tests all Chapter 10 tasks."""

from predicates.prover_test import *
from predicates.some_proofs_test import *

def test_skeleton(debug=False):
    test_prover_basic(debug)

def test_task1(debug=False):
    test_add_universal_instantiation(debug)

def test_task2(debug=False):
    test_add_tautological_implication(debug)

def test_task3(debug=False):
    test_add_existential_derivation(debug)

def test_task4(debug=False):
    test_prove_lovers(debug)

def test_task5(debug=False):
    test_prove_homework(debug)

def test_task6(debug=False):
    test_add_flipped_equality(debug)

def test_task7(debug=False):
    test_add_free_instantiation(debug)

def test_task8(debug=False):
    test_add_substituted_equality(debug)

def test_task9(debug=False):
    test_add_chained_equality(debug)

def test_task10(debug=False):
    test_prove_group_unique_zero(debug)

def test_task11(debug=False):
    test_prove_field_zero_multiplication(debug)

def test_task12(debug=False):
    test_prove_peano_left_neutral(debug)

def test_task13(debug=False):
    test_prove_russell_paradox(debug)

test_skeleton(True)
test_task1(True)
test_task2(True)
test_task3(True)
test_task4(True)
test_task5(True)
test_task6(True)
test_task7(True)
test_task8(True)
test_task9(True)
test_task10(True)
test_task11(True)
test_task12(True)
test_task13(True)
