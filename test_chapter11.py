# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: test_chapter11.py

"""Tests all Chapter 11 tasks."""

from predicates.deduction_test import *
from predicates.prenex_test import *
from predicates.some_proofs_test import *

def test_task1(debug=False):
    test_remove_assumption(debug)

def test_task2(debug=False):
    test_prove_by_way_of_contradiction(debug)

def test_task3(debug=False):
    test_is_quantifier_free(debug)
    test_is_in_prenex_normal_form(debug)

def test_task4(debug=False):
    test_prove_not_exists_not_implies_all(debug)
    test_prove_exists_not_implies_not_all(debug)
    test_prove_not_all_iff_exists_not(debug)

def test_task5(debug=False):
    test_uniquely_rename_quantified_variables(debug)

def test_task6(debug=False):
    test_pull_out_quantifications_across_negation(debug)

def test_task7(debug=False):
    test_pull_out_quantifications_from_left_across_binary_operator(debug)
    test_pull_out_quantifications_from_right_across_binary_operator(debug)

def test_task8(debug=False):
    test_pull_out_quantifications_across_binary_operator(debug)

def test_task9(debug=False):
    test_to_prenex_normal_form_from_uniquely_named_variables(debug)

def test_task10(debug=False):
    test_to_prenex_normal_form(debug)

test_task1(True)
test_task2(True)
test_task3(True)
#test_task4(True) # Optional
test_task5(True)
test_task6(True)
test_task7(True)
test_task8(True)
test_task9(True)
test_task10(True)
