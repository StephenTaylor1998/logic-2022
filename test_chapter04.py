# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: test_chapter04.py

"""Tests all Chapter 4 tasks."""

from propositions.proofs_test import *
from propositions.semantics_test import *
from propositions.some_proofs_test import *
from propositions.soundness_test import *

def test_task1(debug=False):
    test_variables(debug)

def test_task2(debug=False):
    test_evaluate_inference(debug)

def test_task3(debug=False):
    test_is_sound_inference(debug)

def test_task4(debug=False):
    test_specialize(debug)

def test_task5(debug=False):
    test_merge_specialization_maps(debug)
    test_formula_specialization_map(debug)
    test_specialization_map(debug)
    test_is_specialization_of(debug)

def test_task6(debug=False):
    test_rule_for_line(debug)
    test_is_line_valid(debug)
    test_is_valid(debug)
    
def test_task7(debug=False):
    test_prove_and_commutativity(debug)

def test_task8(debug=False):
    test_prove_I0(debug)

def test_task9(debug=False):
    test_rule_nonsoundness_from_specialization_nonsoundness(debug)

def test_task10(debug=False):
    test_nonsound_rule_of_nonsound_proof(debug)

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
