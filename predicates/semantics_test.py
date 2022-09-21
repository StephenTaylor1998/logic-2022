# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/semantics_test.py

"""Tests for the predicates.semantics module."""

from logic_utils import frozendict

from predicates.syntax import *
from predicates.semantics import *

def test_evaluate_term(debug=False):
    model = Model({'0', '1'}, {'c': '1'}, {},
                  {'plus': {('0', '0'): '0', ('0', '1'): '1', ('1', '1'): '0',
                            ('1', '0'): '1'}})
    if debug:
        print('In the model', model)
    for s,expected_value in [['c', '1'], ['plus(c,c)', '0'],
                             ['plus(c,plus(c,c))', '1']]:
        term = Term.parse(s)
        value = model.evaluate_term(term)
        if debug:
            print('The value of', term, 'is', value)
        assert value == expected_value

    assignment = {'x': '1', 'y': '0'}
    for s,expected_value in [['x', '1'], ['plus(x,c)', '0'],
                             ['plus(x,y)', '1']]:
        term = Term.parse(s)
        value = model.evaluate_term(term, assignment)
        if debug:
            print('The value of', term, 'with assignment x=1 y=0 is', value)
        assert value == expected_value

def test_evaluate_formula(debug=False):
    __test_formula_evaluation_common(
        lambda model,formula: model.evaluate_formula(formula),
        'evaluate_formula', debug)

    model = Model({'0', '1', '2'}, {'0': '0'}, {'Pz': {('0',)}},
                  {'p1': {('0',): '1', ('1',): '2', ('2',): '0'}})
    if debug:
        print('In the model', model)
    formula = Formula.parse('Pz(p1(x))')
    for assigned_value,expected_value in [
        ('0', False), ('1', False), ('2', True)]:
        assignment = {'x': assigned_value}
        value = model.evaluate_formula(formula, frozendict(assignment))
        if debug:
            print('The value of', formula, 'with assignment', assignment, 'is',
                  value)
        assert value == expected_value

    universe = {0,1,2}
    pairs = {(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)}
    all_formula = Formula.parse('Ax[Ay[R(x,y)]]')
    exists_formula = Formula.parse('Ex[Ey[~R(x,y)]]')

    model = Model(universe, {}, {'R': pairs})
    if debug:
        print('In the model', model)
    value = model.evaluate_formula(all_formula)
    if debug:
        print('The value of', all_formula, 'is', value)
    assert value
    value = model.evaluate_formula(exists_formula)
    if debug:
        print('The value of', exists_formula, 'is', value)
    assert not value

    for exclude in pairs:
        model = Model(universe, {}, {'R': (pairs-{exclude})})
        if debug:
            print('In the model', model)
        value = model.evaluate_formula(all_formula)
        if debug:
            print('The value of', all_formula, 'is', value)
        assert not value
        value = model.evaluate_formula(exists_formula)
        if debug:
            print('The value of', exists_formula, 'is', value)
        assert value

def test_is_model_of(debug=False):
    __test_formula_evaluation_common(
        lambda model,formula: model.is_model_of(frozenset({formula})),
        'is_model_of', debug)

    pairs = {('a', 'a'), ('a', 'b'), ('b', 'a')}
    model = Model({'a', 'b'}, {'bob': 'a'}, {'Friends': pairs})
    f0 = Formula.parse('Friends(bob,bob)')
    f1 = Formula.parse('Friends(bob,y)')
    f2 = Formula.parse('Friends(x,bob)')
    f3 = Formula.parse('Friends(x,y)')

    if debug:
        print('The model', model, '...')
    for formulas,expected_result in [
            ({f1}, True), ({f2},True), ({f1, f2}, True), ({f3}, False),
            ({f1,f2,f3}, False), ({f0,f3}, False)]:
        result = model.is_model_of(frozenset(formulas))
        if debug:
            print('... is said', '' if result else 'not', 'to satisfy',
                  formulas)
        assert result == expected_result

    formula = Formula.parse('(F(z,a)->z=b)')
    model = Model({'a', 'b'}, {'a': 'a', 'b': 'b'},
                  {'F': {('a', 'a'), ('b', 'b')}})
    if debug:
        print('The model', model, '...')
    result = model.is_model_of(frozenset({formula}))
    if debug:
        print('... is said', '' if result else 'not', 'to satisfy', formula)
    assert not result
    
    universe = {0,1,2}
    pairs = {(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)}
    formula = Formula.parse('R(x,y)')

    model = Model(universe, {}, {'R': pairs})
    if debug:
        print('The model', model, '...')
    result = model.is_model_of(frozenset({formula}))
    if debug:
        print('... is said', '' if result else 'not', 'to satisfy', formula)
    assert result

    for exclude in pairs:
        model = Model(universe, {}, {'R': (pairs-{exclude})})
        if debug:
            print('The model', model, '...')
        result = model.is_model_of(frozenset({formula}))
        if debug:
            print('... is said', '' if result else 'not', 'to satisfy', formula)
        assert not result

def __test_formula_evaluation_common(evaluate, tested_name, debug):
    model = Model({'0', '1', '2'}, {'0': '0'}, {'Pz': {('0',)}},
                  {'p1': {('0',): '1', ('1',): '2', ('2',): '0'}})
    if debug:
        print('According to', tested_name, 'in the model', model)
    for s,expected_value in [
            ('Pz(0)', True), ('0=p1(0)', False), ('(p1(0)=0|0=p1(0))', False),
            ('(p1(0)=0->0=p1(0))', True), ('Ax[Ey[p1(y)=x]]', True),
            ('Ex[(x=p1(0)&Ex[x=0])]', True), ('Ax[(x=p1(0)|Ex[x=0])]', True),
            ('Ex[(x=p1(0)&Ax[(x=0|x=p1(0))])]', False),
            ('Ex[(x=p1(0)&Ax[((x=0|x=p1(0))|x=p1(p1(0)))])]', True),
            ('Ax[(x=p1(0)->Ex[x=0])]', True),
            ('Ax[(x=0->Ax[(x=p1(0)->Ex[(x=0&Ax[(x=0|x=p1(0))])])])]', False),
            ('Ax[(x=0->Ax[(x=p1(0)->'
             'Ex[(x=0&Ax[((x=0|x=p1(0))|x=p1(p1(0)))])])])]', True)]:
        formula = Formula.parse(s)
        value = evaluate(model, formula)
        if debug:
            print('The value of', formula, 'is', value)
        assert value == expected_value

def test_ex7(debug=False):
    test_evaluate_term(debug)
    test_evaluate_formula(debug)
    test_is_model_of(debug)

def test_all(debug=False):
    test_ex7(debug)
