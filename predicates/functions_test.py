# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/functions_test.py

"""Tests for the predicates.functions module."""

from predicates.syntax import *
from predicates.semantics import *
from predicates.functions import *

def test_replace_functions_with_relations_in_model(debug=False):
    model = Model(
        {'a', 'b'}, {'a': 'a'}, {'GT': {('b','a')}},
        {'f': {('a',):'b', ('b',):'b'},
         'gg': {('a','a'):'b', ('a','b'):'a', ('b','a'):'a', ('b','b'):'b'}})
    if debug:
        print('Replacing functions with relations in model', model, '...')
    new_model = replace_functions_with_relations_in_model(model)
    if debug:
        print('... got', new_model)
    assert new_model.universe == model.universe
    assert new_model.constant_interpretations.keys() == {'a'}
    assert new_model.constant_interpretations['a'] == 'a'
    assert new_model.relation_interpretations.keys() == {'F', 'Gg', 'GT'}
    assert new_model.relation_interpretations['F'] == {('b','a'), ('b','b')}
    assert new_model.relation_interpretations['Gg'] == \
           {('b','a','a'), ('a','a','b'), ('a','b','a'), ('b','b','b')}
    assert new_model.relation_interpretations['GT'] == {('b','a')}
    assert len(new_model.function_interpretations) == 0
    
def test_replace_relations_with_functions_in_model(debug=False):
    model = Model(
        {'a', 'b'}, {'a': 'a'},
        {'GT': {('b','a')}, 'F' :{('b','a'), ('b','b')},
         'GG': {('b','a','a'), ('a','a','b'), ('a','b','a'), ('b','b','b')}})

    if debug:
        print('Replacing relations F, GG with functions in model', model, '...')
    new_model = \
        replace_relations_with_functions_in_model(model, frozenset({'f', 'gG'}))
    if debug:
        print('... got', new_model)
    assert new_model.universe == model.universe
    assert new_model.constant_interpretations.keys() == {'a'}
    assert new_model.constant_interpretations['a'] == 'a'
    assert new_model.relation_interpretations.keys() == {'GT'}
    assert new_model.relation_interpretations['GT'] == {('b','a')}
    assert new_model.function_interpretations.keys() == {'f', 'gG'}
    assert new_model.function_interpretations['f'] == {('a',):'b', ('b',):'b'}
    assert new_model.function_interpretations['gG'] == \
           {('a','a'):'b', ('a','b'):'a', ('b','a'):'a', ('b','b'):'b'}

    if debug:
        print('Replacing relation F with function in model', model, '...')
    new_model = \
        replace_relations_with_functions_in_model(model, frozenset({'f'}))
    if debug:
        print('... got', new_model)
    assert new_model.universe == model.universe
    assert new_model.constant_interpretations.keys() == {'a'}
    assert new_model.constant_interpretations['a'] == 'a'
    assert new_model.relation_interpretations.keys() == {'GG', 'GT'}
    assert new_model.relation_interpretations['GG'] == \
           {('b','a','a'), ('a','a','b'), ('a','b','a'), ('b','b','b')}
    assert new_model.relation_interpretations['GT'] == {('b','a')}
    assert new_model.function_interpretations.keys() == {'f'}

    # Test faulty models
    model = Model(
        {'a', 'b'}, {'a': 'a'},
        {'GT': {('b','a')}, 'F' :{('b','a'), ('b','b'), ('a','b')},
         'GG': {('b','a','a'), ('a','a','b'), ('a','b','a'), ('b','b','b')}})
    if debug:
        print('Replacing relations with functions in model', model, '...')
    new_model = \
        replace_relations_with_functions_in_model(model, frozenset({'f', 'gG'}))
    assert new_model == None

    model = Model(
        {'a', 'b'}, {'a': 'a'},
        {'GT': {('b','a')}, 'F' :{('b','a'), ('b','b')},
         'GG': {('b','a','a'), ('a','a','b'), ('b','b','b')}})
    if debug:
        print('Replacing relations F, GG with functions in model', model, '...')
    new_model = \
        replace_relations_with_functions_in_model(model, frozenset({'f', 'gG'}))
    assert new_model == None

def test_compile_term(debug=False):
    from logic_utils import fresh_variable_name_generator
    from predicates.functions import _compile_term
    fresh_variable_name_generator._reset_for_test()

    for s,expected in [
            ['f(x,g(0))', ['z1=g(0)', 'z2=f(x,z1)']],
            ['f(g(x,h(0)),f(f(0,g(y)),h(h(x))))',
             ['z3=h(0)', 'z4=g(x,z3)', 'z5=g(y)', 'z6=f(0,z5)', 'z7=h(x)',
              'z8=h(z7)', 'z9=f(z6,z8)', 'z10=f(z4,z9)']],
            ['f(x,g(0))', ['z11=g(0)', 'z12=f(x,z11)']]]:
        term = Term.parse(s)
        if debug:
            print('Compiling', term, '...')
        steps = _compile_term(term)
        if debug:
            print('... got', steps)
        assert steps == [Formula.parse(e) for e in expected]

def test_replace_functions_with_relations_in_formula(debug=False):
    for s,valid_model,invalid_model in [
        ['b=f(a)',
         Model({'a', 'b'}, {'a': 'a', 'b': 'b'}, {'F':{('b','a'), ('b','b')}}),
         Model({'a', 'b'}, {'a': 'a', 'b': 'b'}, {'F':{('a','a'), ('b','b')}})],
        ['GT(f(a),g(b))',
         Model({'a', 'b'}, {'a': 'a', 'b': 'b'},
               {'GT': {('b','a')}, 'F': {('b','a'), ('b','b')},
                'G': {('b','a'), ('a','b')}}),
         Model({'a', 'b'}, {'a': 'a', 'b': 'b'},
               {'GT': {('b','a')}, 'F': {('a','a'), ('b','b')},
                'G': {('b','a'), ('a','b')}})],
        ['Ax[f(f(x))=x]',
         Model({'a', 'b'}, {'a': 'a', 'b': 'b'},
               {'GT': {('b','a')}, 'F': {('a','a'), ('b','b')},
                'G': {('b','a'), ('a','b')}}),
         Model({'a', 'b'}, {'a': 'a', 'b': 'b'},
               {'GT': {('b','a')}, 'F': {('b','a'), ('b','b')},
                'G': {('b','a'), ('a','b')}})],
        ['f(f(x))=x',
         Model({'a', 'b'}, {'a': 'a', 'b': 'b'},
               {'GT': {('b','a')}, 'F': {('a','a'), ('b','b')},
                'G': {('b','a'), ('a','b')}}),
         Model({'a', 'b'}, {'a': 'a', 'b': 'b'},
               {'GT': {('b','a')}, 'F': {('b','a'), ('b','b')},
                'G': {('b','a'), ('a','b')}})],
        ['Ax[(Ey[f(y)=x]->GT(x,a))]',
         Model({'a', 'b'}, {'a': 'a', 'b': 'b'},
               {'GT': {('b','a')}, 'F': {('b','a'), ('b','b')},
                'G': {('b','a'), ('a','b')}}),
         Model({'a', 'b'}, {'a': 'a', 'b': 'b'},
               {'GT': {('b','a')}, 'F': {('a','a'), ('b','b')},
                'G': {('b','a'), ('a','b')}})]]:
        formula = Formula.parse(s)
        if debug:
            print('Replacing functions with relations in formula', formula,
                  '...')
        new_formula = replace_functions_with_relations_in_formula(formula)
        if debug:
            print('... got', new_formula)
        for model,validity in [[valid_model,True], [invalid_model,False]]:
            is_valid_model = model.is_model_of({new_formula})
            if debug:
                print('which', 'is' if is_valid_model else 'is not',
                      'satisfied by model', model)
            assert is_valid_model == validity

def test_replace_functions_with_relations_in_formulas(debug=False):
    formula = Formula.parse('GT(f(a),g(b))')
    if debug:
        print('Removing functions from singleton', formula, '...')
    new_formulas = \
        replace_functions_with_relations_in_formulas(frozenset({formula}))
    if debug:
        print('... got', new_formulas)

    for model,validity in [
            [Model({'a', 'b'}, {'a': 'a', 'b': 'b'},
                   {'GT': {('b','a')}, 'F': {('b','a'), ('a','b')},
                    'G': {('b','a'), ('a','b')}}),
             True],
            [Model({'a', 'b'}, {'a': 'a', 'b': 'b'},
                   {'GT': {('b','a')}, 'F': {('a','a'), ('b','b')},
                    'G': {('b','a'), ('a','b')}}),
             False],
            [Model({'a', 'b'}, {'a': 'a', 'b': 'b'},
                   {'GT': {('b','a')}, 'F': {('b','a')},
                    'G': {('b','a'), ('a','b')}}),
             False],
            [Model({'a', 'b'}, {'a': 'a', 'b': 'b'},
                   {'GT': {('b','a')}, 'F': {('b','a'), ('b','b'), ('a','b')},
                    'G': {('b','a'), ('a','b')}}),
             False],
            [Model({'a', 'b'}, {'a': 'a', 'b': 'b'},
                   {'GT': {('b','a')}, 'F': {('b','a'), ('b','b')},
                    'G': {('b','a'), ('a','b'), ('b','b')}}),
             False]]:
        if debug:
            print('which',
                  'is' if model.is_model_of(new_formulas) else 'is not',
                  'satisfied by model', model)
        assert model.is_model_of(new_formulas) == validity

def test_replace_equality_with_SAME_in_formulas(debug=False):
    formula = Formula.parse('Ax[Ay[Az[((S(x,y)&S(x,z))->y=z)]]]')
    if debug:
        print('Removing equalities from singleton', formula, '...')
    new_formulas = replace_equality_with_SAME_in_formulas(frozenset({formula}))
    if debug:
        print('... got', new_formulas)
    assert Formula.parse('Ax[Ay[Az[((S(x,y)&S(x,z))->SAME(y,z))]]]') in \
           new_formulas

    for model,validity in [
            [Model({'0', '1', '2'}, {},
                   {'S': set(),
                    'SAME': {('0','0'), ('1','1'), ('2','2'), ('0','1')}}),
             False],
            [Model({'0', '1', '2'}, {},
                   {'S': set(), 'SAME': {('0','0'), ('1','1')}}),
             False],
            [Model({'0', '1', '2'}, {},
                   {'S': set(),
                    'SAME': {('0','0'), ('1','1'), ('2','2'),
                             ('0','1'), ('1','0'), ('2','1'), ('1','2')}}),
             False],
            [Model({'0', '1', '2'}, {},
                   {'S': set(), 'SAME': {('0','0'), ('1','1'), ('2','2')}}),
             True],
            [Model({'0', '1', '2'}, {},
                   {'S': {('0','1'), ('0','2')},
                    'SAME': {('0','0'), ('1','1'), ('2','2')}}),
             False],
            [Model({'0', '1', '2'}, {},
                   {'S': {('0','1'),('0','2')},
                    'SAME': {('0','0'), ('1','1'), ('2','2'), ('1','2'),
                             ('2','1')}}),
             True],
            [Model({'0', '1', '2'}, {},
                   {'S': {('0','1')},
                    'SAME': {('0','0'), ('1','1'), ('2','2'), ('1','2'),
                             ('2','1')}}),
             False]]:
        if debug:
            print('which',
                  'is' if model.is_model_of(new_formulas) else 'is not',
                  'satisfied by model', model)
        assert model.is_model_of(new_formulas) == validity
  
def test_add_SAME_as_equality_in_model(debug=False):
    model = Model({'0', '1', '2'}, {'a': '0'}, {'Q': {('1',)}})
    if debug:
        print('Adding SAME to model', model, '...')
    new_model = add_SAME_as_equality_in_model(model)
    if debug:
        print('... got', new_model)
    assert new_model.universe == model.universe
    assert new_model.constant_interpretations.keys() == {'a'}
    assert new_model.constant_interpretations['a'] == \
           model.constant_interpretations['a']
    assert new_model.relation_interpretations.keys() == {'Q', 'SAME'}
    assert new_model.relation_interpretations['Q'] == \
           model.relation_interpretations['Q']
    assert new_model.relation_interpretations['SAME'] == \
           {('0','0'), ('1','1'), ('2','2')}
    assert len(new_model.function_interpretations) == 0

def test_make_equality_as_SAME_in_model(debug=False):
    model = Model({'0', '1', '2'}, {'a': '0', 'b': '1', 'c': '2'},
                  {'SAME': {('0','0'), ('1','1'), ('2','2'), ('1','2'),
                            ('2','1')},
                   'Q': {('0',), ('1',), ('2',)}})
    if debug:
        print('Making equality as SAME in model', model)
    new_model = make_equality_as_SAME_in_model(model)
    if debug:
        print('... got', new_model)
    assert len(new_model.universe) == 2
    assert new_model.constant_interpretations.keys() == {'a', 'b', 'c'}
    assert new_model.constant_interpretations['b'] == \
           new_model.constant_interpretations['c']
    assert new_model.constant_interpretations['a'] != \
           new_model.constant_interpretations['b']
    assert new_model.relation_interpretations.keys() == {'Q'}
    for x in new_model.universe:
        assert (x,) in new_model.relation_interpretations['Q']
    assert len(new_model.relation_interpretations['Q']) == 2
    assert len(new_model.function_interpretations) == 0

def test_all(debug=False):
    test_replace_functions_with_relations_in_model(debug)
    test_replace_relations_with_functions_in_model(debug)
    test_compile_term(debug)
    test_replace_functions_with_relations_in_formula(debug)
    test_replace_functions_with_relations_in_formulas(debug)
    test_replace_equality_with_SAME_in_formulas(debug)
    test_add_SAME_as_equality_in_model(debug)
    test_make_equality_as_SAME_in_model(debug)
