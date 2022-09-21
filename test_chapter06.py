# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: test_chapter06.py

"""Tests all Chapter 6 tasks."""

from propositions.proofs_test import test_is_valid
from propositions.tautology_test import *
from propositions.some_proofs_test import *

def pretest_validity(debug=False):
    test_is_valid(debug)

def test_task1(debug=False):
    test_formulas_capturing_model(debug)
    test_prove_in_model(debug)
    
def test_task2(debug=False):
    test_reduce_assumption(debug)

def test_task3(debug=False):
    test_prove_tautology(debug)
    test_proof_or_counterexample(debug)

def test_task4(debug=False):
    test_encode_as_formula(debug)
    test_prove_sound_inference(debug)

def test_task5(debug=False):
    test_model_or_inconsistency(debug)

def test_task6(debug=False):
    test_prove_in_model_full(debug)

def test_task7(debug=False):
    test_prove_I2(debug)
    test_prove_NNE(debug)
    test_prove_NN(debug)
    test_prove_CP(debug)
    test_prove_NI(debug)
    test_prove_CM(debug)
    test_prove_R(debug)

def test_task8(debug=False):
    test_prove_N(debug)

def test_task9(debug=False):
    test_prove_NA1(debug)
    test_prove_NA2(debug)
    test_prove_NO(debug)

pretest_validity(False)
test_task1(True)
test_task2(True)
test_task3(True)
test_task4(True)
test_task5(True)
#test_task6(True) # Optional
#test_task7(True) # Optional
#test_task8(True) # Optional
#test_task9(True) # Optional
