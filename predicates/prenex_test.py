# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/prenex_test.py

"""Tests for the predicates.prenex module."""

from predicates.prenex import *

def test_is_quantifier_free(debug=False):
    for formula,free in [
            ('x=y', True),
            ('SAME(x,y)', True),
            ('Ax[x=y]', False),
            ('(R(x)|Q(y))', True),
            ('(R(x)|Ey[Q(y)])', False),
            ('(Ax[R(x)]|Q(y))', False),
            ('(R(x)|((R(z)&~P(c))->Q(y)))', True),
            ('(R(x)|((R(z)&~Az[P(c)])->Q(y)))', False),
            ('Ax[Ey[Az[(R(x)|((R(z)&~P(c))->Q(y)))]]]', False),
            ('Ax[Ey[Az[(R(x)|((R(z)&~Az[P(c)])->Q(y)))]]]', False)]:
        formula = Formula.parse(formula)
        if debug:
            print('Testing is_quantifier_free on the formula', formula)
        assert is_quantifier_free(formula) == free

def test_is_in_prenex_normal_form(debug=False):
    for formula,prenex in [
            ('x=y', True),
            ('R(x,y)', True),
            ('Ax[x=y]', True),
            ('(R(x)|Q(y))', True),
            ('(R(x)|Ey[Q(y)])', False),
            ('(Ax[R(x)]|Q(y))', False),
            ('(R(x)|((R(z)&~P(c))->Q(y)))', True),
            ('(R(x)|((R(z)&~Az[P(c)])->Q(y)))', False),
            ('Ax[Ey[Az[(R(x)|((R(z)&~P(c))->Q(y)))]]]', True),
            ('Ax[Ey[Az[(R(x)|((R(z)&~Az[P(c)])->Q(y)))]]]', False)]:
        formula = Formula.parse(formula)
        if debug:
            print('Testing is_in_prenex_normal_form on the formula', formula)
        assert is_in_prenex_normal_form(formula) == prenex

def test_uniquely_rename_quantified_variables(debug=False):
    from predicates.prenex import _uniquely_rename_quantified_variables

    for formula in ['Ax[Q(x,y)]',
                    'Q(x,c)',
                    'Ax[(Ay[R(x,y)]&w=7)]',
                    '(Ax[(Ax[R(x)]&x=7)]|x=6)',
                    '(Ex[R(x)]&Ex[Q(x)])',
                    '~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])',
                    '~(w=y|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])']:
        formula = Formula.parse(formula)
        if debug:
            print('Testing _uniquely_rename_quantified_variables on', formula,
                  '...')
        result,proof = _uniquely_rename_quantified_variables(formula)
        if debug:
            print('... got', result)
        assert has_uniquely_named_variables(result)
        _test_substitution(formula, result, {})
        assert proof.assumptions == \
            Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
        assert proof.conclusion == equivalence_of(formula, result)
        assert proof.is_valid()

def test_pull_out_quantifications_across_negation(debug=False):
    from predicates.prenex import _pull_out_quantifications_across_negation

    for formula,expected in [
        ('~Q(x,c)', '~Q(x,c)'), ('~Ax[Q(x)]', 'Ex[~Q(x)]'),
        ('~Ex[Q(x)]', 'Ax[~Q(x)]'),
        ('~Ax[Ey[Az[(f(x,y)=z&Q(y))]]]', 'Ex[Ay[Ez[~(f(x,y)=z&Q(y))]]]')]:
        formula = Formula.parse(formula)
        if debug:
            print('Testing _pull_out_quantifications_across_negation on',
                   formula, '...')
        result,proof = _pull_out_quantifications_across_negation(formula)
        if debug:
            print('... got', result)
        assert str(result) == expected
        assert proof.assumptions == \
            Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
        assert proof.conclusion == equivalence_of(formula, result)
        assert proof.is_valid()

def test_pull_out_quantifications_from_left_across_binary_operator(debug=False):
    from predicates.prenex import \
         _pull_out_quantifications_from_left_across_binary_operator

    for formula,expected in [
        ('(Q(x,c)|R(d,y))', '(Q(x,c)|R(d,y))'),
        ('(Ax[T(x)]&S())', 'Ax[(T(x)&S())]'),
        ('(Ex[T(x)]&S())', 'Ex[(T(x)&S())]'),
        ('(Ax[T(x)]|S())', 'Ax[(T(x)|S())]'),
        ('(Ex[T(x)]|S())', 'Ex[(T(x)|S())]'),
        ('(Ax[T(x)]->S())', 'Ex[(T(x)->S())]'),
        ('(Ex[T(x)]->S())', 'Ax[(T(x)->S())]'),
        ('(Ax[Ey[R(x,y)]]&Az[Ew[z=w]])', 'Ax[Ey[(R(x,y)&Az[Ew[z=w]])]]'),
        ('(Ax[Ey[R(x,y)]]|Az[Ew[z=w]])', 'Ax[Ey[(R(x,y)|Az[Ew[z=w]])]]'),
        ('(Ax[Ey[R(x,y)]]->Az[Ew[z=w]])', 'Ex[Ay[(R(x,y)->Az[Ew[z=w]])]]')]:
        formula = Formula.parse(formula)
        if debug:
            print('Testing '
                  '_pull_out_quantifications_from_left_across_binary_operator'
                  'on', formula, '...')
        result,proof = \
            _pull_out_quantifications_from_left_across_binary_operator(formula)
        if debug:
            print('... got', result)
        assert str(result) == expected
        assert proof.assumptions == \
            Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
        assert proof.conclusion == equivalence_of(formula, result)
        assert proof.is_valid()

def test_pull_out_quantifications_from_right_across_binary_operator(debug=
                                                                    False):
    from predicates.prenex import \
         _pull_out_quantifications_from_right_across_binary_operator

    for formula,expected in [
        ('(Q(x,c)|R(d,y))', '(Q(x,c)|R(d,y))'),
        ('(S()&Ax[T(x)])', 'Ax[(S()&T(x))]'),
        ('(S()&Ex[T(x)])', 'Ex[(S()&T(x))]'),
        ('(S()|Ax[T(x)])', 'Ax[(S()|T(x))]'),
        ('(S()|Ex[T(x)])', 'Ex[(S()|T(x))]'),
        ('(S()->Ax[T(x)])', 'Ax[(S()->T(x))]'),
        ('(S()->Ex[T(x)])', 'Ex[(S()->T(x))]'),
        ('(Ax[Ey[R(x,y)]]&Az[Ew[z=w]])', 'Az[Ew[(Ax[Ey[R(x,y)]]&z=w)]]'),
        ('(Ax[Ey[R(x,y)]]|Az[Ew[z=w]])', 'Az[Ew[(Ax[Ey[R(x,y)]]|z=w)]]'),
        ('(Ax[Ey[R(x,y)]]->Az[Ew[z=w]])', 'Az[Ew[(Ax[Ey[R(x,y)]]->z=w)]]')]:
        formula = Formula.parse(formula)
        if debug:
            print('Testing '
                  '_pull_out_quantifications_from_right_across_binary_operator '
                  'on', formula, '...')
        result,proof = \
            _pull_out_quantifications_from_right_across_binary_operator(formula)
        if debug:
            print('... got', result)
        assert str(result) == expected
        assert proof.assumptions == \
            Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
        assert proof.conclusion == equivalence_of(formula, result)
        assert proof.is_valid()

def test_pull_out_quantifications_across_binary_operator(debug=False):
    from predicates.prenex import \
         _pull_out_quantifications_across_binary_operator

    for formula,expected in [
        ('(Q(x,c)|R(d,y))', '(Q(x,c)|R(d,y))'),
        ('(Ax[S(x)]&Ay[T(y)])', 'Ax[Ay[(S(x)&T(y))]]'),
        ('(Ax[Ey[R(x,y)]]&Az[z=c])', 'Ax[Ey[Az[(R(x,y)&z=c)]]]'),
        ('(Ax[Ey[R(x,y)]]&Az[Ew[z=w]])', 'Ax[Ey[Az[Ew[(R(x,y)&z=w)]]]]'),
        ('(Ax[Ey[R(x,y)]]|Az[Ew[z=w]])', 'Ax[Ey[Az[Ew[(R(x,y)|z=w)]]]]'),
        ('(Ax[Ey[R(x,y)]]->Az[Ew[z=w]])', 'Ex[Ay[Az[Ew[(R(x,y)->z=w)]]]]')]:
        formula = Formula.parse(formula)
        if debug:
            print('Testing _pull_out_quantifications_across_binary_operator on',
                  formula, '...')
        result,proof = _pull_out_quantifications_across_binary_operator(formula)
        if debug:
            print('... got', result)
        assert str(result) == expected
        assert proof.assumptions == \
            Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
        assert proof.conclusion == equivalence_of(formula, result)
        assert proof.is_valid()

def test_to_prenex_normal_form_from_uniquely_named_variables(debug=False):
    from predicates.prenex import \
         _to_prenex_normal_form_from_uniquely_named_variables

    for formula,pnf in [
        ('Q(x,c)', 'Q(x,c)'),
        ('Ax[Q(x,c)]', 'Ax[Q(x,c)]'),
        ('~~(~Ax[Ey[R(x,y)]]&~Az[Ew[z=w]])',
         'Ex[Ay[Ez[Aw[~~(~R(x,y)&~z=w)]]]]'),
        ('~~(~Ax[Ey[R(x,y)]]|~Az[Ew[z=w]])',
         'Ex[Ay[Ez[Aw[~~(~R(x,y)|~z=w)]]]]'),
        ('~~(~Ax[Ey[R(x,y)]]->~Az[Ew[z=w]])',
         'Ax[Ey[Ez[Aw[~~(~R(x,y)->~z=w)]]]]'),
        ('~(z=x|Au[(Ezz[(zz=u&Aw[w=zz])]->Auu[uu=y])])',
         'Eu[Ezz[Aw[Euu[~(z=x|((zz=u&w=zz)->uu=y))]]]]')]:
        formula = Formula.parse(formula)
        if debug:
            print('Testing '
                  '_to_prenex_normal_form_from_uniquely_named_variables on',
                  formula, '...')
        result,proof = \
            _to_prenex_normal_form_from_uniquely_named_variables(formula)
        if debug:
            print('... got', result)
        assert is_in_prenex_normal_form(result)
        assert str(result) == pnf
        assert proof.assumptions == \
            Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
        assert proof.conclusion == equivalence_of(formula, result)
        assert proof.is_valid()

def test_to_prenex_normal_form(debug=False):
    for formula,pnf in [
        ('Q(x,c)', 'Q(x,c)'),
        ('Ax[Q(x,c)]', 'Ax[Q(x,c)]'),
        ('~~(~Ax[Ey[R(x,y)]]&~Ax[Ey[x=y]])',
         'Ex[Ay[Eu[Aw[~~(~R(x,y)&~u=w)]]]]'),
        ('~~(~Ax[Ey[R(x,y)]]|~Ax[Ey[x=y]])',
         'Ex[Ay[Eu[Aw[~~(~R(x,y)|~u=w)]]]]'),
        ('~~(~Ax[Ey[R(x,y)]]->~Ax[Ey[x=y]])',
         'Ax[Ey[Eu[Aw[~~(~R(x,y)->~u=w)]]]]'),
        ('(Ax[(Ax[R(x)]&x=7)]|x=6)', 'Ax1[Ax2[((R(x2)&x1=7)|x=6)]]'),
        ('~(u=x|Au[(Ex[(x=u&Au[u=x])]->Ax[x=y])])',
         'Eu1[Ex1[Au2[Ex2[~(u=x|((x1=u1&u2=x1)->x2=y))]]]]')]:
        formula = Formula.parse(formula)
        if debug:
            print('Testing to_prenex_normal_form on', formula, '...')
        result,proof = to_prenex_normal_form(formula)
        if debug:
            print('... got', result)
        assert is_in_prenex_normal_form(result)
        assert has_uniquely_named_variables(result)
        _test_substitution(Formula.parse(pnf), result, {})
        assert proof.assumptions == \
            Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
        assert proof.conclusion == equivalence_of(formula, result)
        assert proof.is_valid()

def _test_substitution(original, new, substitution_map):
    assert original.root == new.root
    if is_relation(original.root) or is_equality(original.root):
        assert original.substitute(substitution_map) == new
    elif is_unary(original.root):
        _test_substitution(original.first, new.first, substitution_map)
    elif is_binary(original.root):
        _test_substitution(original.first, new.first, substitution_map)
        _test_substitution(original.second, new.second, substitution_map)
    else:
        assert is_quantifier(original.root)
        substitution_map = substitution_map.copy()
        substitution_map[original.variable] = Term(new.variable)
        _test_substitution(original.statement, new.statement, substitution_map)

def test_ex11(debug=False):
    test_is_quantifier_free(debug)
    test_is_in_prenex_normal_form(debug)
    test_uniquely_rename_quantified_variables(debug)
    test_pull_out_quantifications_across_negation(debug)
    test_pull_out_quantifications_from_left_across_binary_operator(debug)
    test_pull_out_quantifications_from_right_across_binary_operator(debug)
    test_pull_out_quantifications_across_binary_operator(debug)
    test_to_prenex_normal_form_from_uniquely_named_variables(debug)
    test_to_prenex_normal_form(debug)

def test_all(debug=False):
    test_ex11(debug)
