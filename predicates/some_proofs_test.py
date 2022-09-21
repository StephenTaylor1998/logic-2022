# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/some_proofs_test.py

"""Tests for the predicates.some_proofs module."""

from predicates.some_proofs import *

def test_prove_lovers(debug=False):
    proof = prove_lovers(debug)
    assert proof.assumptions == Prover.AXIOMS.union(
        {Schema(Formula.parse('Ax[Ey[Loves(x,y)]]')),
         Schema(Formula.parse('Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'))})
    assert str(proof.conclusion) == 'Ax[Az[Loves(z,x)]]'
    assert proof.is_valid()

def test_prove_homework(debug=False):
    proof = prove_homework(debug)
    assert proof.assumptions == Prover.AXIOMS.union(
        {Schema(Formula.parse('~Ex[(Homework(x)&Fun(x))]')),
         Schema(Formula.parse('Ex[(Homework(x)&Reading(x))]'))})
    assert str(proof.conclusion) == 'Ex[(Reading(x)&~Fun(x))]'
    assert proof.is_valid()

def test_prove_group_unique_zero(debug=False):
    proof = prove_group_unique_zero(debug)
    assert proof.assumptions == Prover.AXIOMS.union(
        {Schema(Formula.parse(a)) for a in GROUP_AXIOMS},
        {Schema(Formula.parse('plus(a,c)=a'))})
    assert str(proof.conclusion) == 'c=0'
    assert proof.is_valid()

def test_prove_field_zero_multiplication(debug=False):
    proof = prove_field_zero_multiplication(debug)
    assert proof.assumptions == Prover.AXIOMS.union(
        {Schema(Formula.parse(a)) for a in FIELD_AXIOMS})
    assert str(proof.conclusion) == 'times(0,x)=0'
    assert proof.is_valid()

def test_prove_peano_left_neutral(debug=False):
    proof = prove_peano_left_neutral(debug)
    assert proof.assumptions == Prover.AXIOMS.union(
        {Schema(Formula.parse(a)) if type(a) is str else a
         for a in PEANO_AXIOMS})
    assert str(proof.conclusion) == 'plus(0,x)=x'
    assert proof.is_valid()

def test_prove_russell_paradox(debug=False):
    proof = prove_russell_paradox(debug)
    assert proof.assumptions == Prover.AXIOMS.union({COMPREHENSION_AXIOM})
    for line in proof.lines:
        if isinstance(line, Proof.AssumptionLine) and \
           line.assumption == COMPREHENSION_AXIOM:
           assert line.instantiation_map['R'] == Formula.parse('~In(_,_)')
    assert str(proof.conclusion) == '(z=z&~z=z)'
    assert proof.is_valid()

def test_prove_not_exists_not_implies_all(debug=False):
    from predicates.some_proofs import _prove_not_exists_not_implies_all

    for formula,variable,equivalence in [
        ('R(x)', 'x', '(~Ex[~R(x)]->Ax[R(x)])'),
        ('Q(y)', 'y', '(~Ey[~Q(y)]->Ay[Q(y)])')]:
        formula = Formula.parse(formula)
        if debug:
            print('Testing _prove_not_exists_not_implies_all to prove',
                  equivalence)
        proof = _prove_not_exists_not_implies_all(variable, formula, debug)
        assert proof.assumptions == Prover.AXIOMS
        assert str(proof.conclusion) == equivalence
        assert proof.is_valid()

def test_prove_exists_not_implies_not_all(debug=False):
    from predicates.some_proofs import _prove_exists_not_implies_not_all

    for formula,variable,equivalence in [
        ('R(x)', 'x', '(Ex[~R(x)]->~Ax[R(x)])'),
        ('Q(y)', 'y', '(Ey[~Q(y)]->~Ay[Q(y)])')]:
        formula = Formula.parse(formula)
        if debug:
            print('Testing _prove_exists_not_implies_not_all to prove',
                  equivalence)
        proof = _prove_exists_not_implies_not_all(variable, formula, debug)
        assert proof.assumptions == Prover.AXIOMS
        assert str(proof.conclusion) == equivalence
        assert proof.is_valid()

def test_prove_not_all_iff_exists_not(debug=False):
    for formula,variable,equivalence in [
        ('R(x)', 'x', '((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
        ('Q(y)', 'y', '((~Ay[Q(y)]->Ey[~Q(y)])&(Ey[~Q(y)]->~Ay[Q(y)]))')]:
        formula = Formula.parse(formula)
        if debug:
            print('Testing prove_not_all_iff_exists_not to prove',
                  equivalence)
        proof = prove_not_all_iff_exists_not(variable, formula, debug)
        assert proof.assumptions == Prover.AXIOMS
        assert str(proof.conclusion) == equivalence
        assert proof.is_valid()

def test_ex10(debug=False):
    test_prove_lovers(debug)
    test_prove_homework(debug)
    test_prove_group_unique_zero(debug)
    test_prove_field_zero_multiplication(debug)
    test_prove_peano_left_neutral(debug)
    test_prove_russell_paradox(debug)

def test_ex11_opt(debug=False):
    test_prove_not_exists_not_implies_all(debug)
    test_prove_exists_not_implies_not_all(debug)
    test_prove_not_all_iff_exists_not(debug)

def test_all(debug=False):
    test_ex10(debug)
    test_ex11_opt(debug)
