# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/deduction_test.py

"""Tests for the predicates.deduction module."""

from predicates.deduction import *

def test_remove_assumption(debug=False):
    from predicates.some_proofs import \
         prove_syllogism, prove_syllogism_with_universal_instantiation,\
         prove_syllogism_all_all,\
         prove_syllogism_all_all_with_tautological_implication,\
         prove_syllogism_all_exists,\
         prove_syllogism_all_exists_with_existential_derivation,\
         prove_lovers, prove_homework, GROUP_AXIOMS, prove_group_unique_zero
    from predicates.some_proofs_test import \
         test_prove_lovers, test_prove_homework, test_prove_group_unique_zero

    # Test one invocation
    test_prove_group_unique_zero()
    proof = prove_group_unique_zero()
    if (debug):
        print("Testing remove_assumption with assumption 'plus(a,c)=a' for the "
              'following proof:\n' + str(proof))
    result = remove_assumption(proof, Formula.parse('plus(a,c)=a'), debug)
    assert result.assumptions == \
           Prover.AXIOMS.union({Schema(Formula.parse(a)) for a in GROUP_AXIOMS})
    assert str(result.conclusion) == '(plus(a,c)=a->c=0)'
    assert result.is_valid()

    # Test two concurrent invocations
    test_prove_lovers()
    test_prove_homework()
    for proof,assumption1,assumption2 in [
            (prove_syllogism(), 'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'),
            (prove_syllogism(), 'Man(aristotle)', 'Ax[(Man(x)->Mortal(x))]'),
            (prove_syllogism_with_universal_instantiation(),
             'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'),
            (prove_syllogism_with_universal_instantiation(),
             'Man(aristotle)', 'Ax[(Man(x)->Mortal(x))]'),
            (prove_syllogism_all_all(),
             'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'),
            (prove_syllogism_all_all(),
             'Ax[(Human(x)->Mortal(x))]', 'Ax[(Greek(x)->Human(x))]'),
            (prove_syllogism_all_all_with_tautological_implication(),
             'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'),
            (prove_syllogism_all_all_with_tautological_implication(),
             'Ax[(Human(x)->Mortal(x))]', 'Ax[(Greek(x)->Human(x))]'),
            (prove_syllogism_all_exists(),
             'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'),
            (prove_syllogism_all_exists(),
             'Ex[Man(x)]', 'Ax[(Man(x)->Mortal(x))]'),
            (prove_syllogism_all_exists_with_existential_derivation(),
             'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'),
            (prove_syllogism_all_exists_with_existential_derivation(),
             'Ex[Man(x)]', 'Ax[(Man(x)->Mortal(x))]'),
            (prove_lovers(),
             'Ax[Ey[Loves(x,y)]]', 'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'),
            (prove_lovers(),
             'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]', 'Ax[Ey[Loves(x,y)]]'),
            (prove_homework(),
             '~Ex[(Homework(x)&Fun(x))]', 'Ex[(Homework(x)&Reading(x))]'),
            (prove_homework(),
             'Ex[(Homework(x)&Reading(x))]', '~Ex[(Homework(x)&Fun(x))]')]:
        if (debug):
            print("Testing remove_assumption with assumption '" + assumption1 +
                  "' for the following proof:\n" + str(proof))
        assumption1 = Formula.parse(assumption1)
        assumption2 = Formula.parse(assumption2)
        result1 = remove_assumption(proof, assumption1)
        assert result1.assumptions == Prover.AXIOMS.union({Schema(assumption2)})
        assert result1.conclusion == Formula('->', assumption1,
                                             proof.conclusion)
        assert result1.is_valid()

        if (debug):
            print("Testing remove_assumption with assumption '" +
                  str(assumption2) + "'for the following proof:\n" +
                  str(result1))
        result2 = remove_assumption(result1, assumption2)
        assert result2.assumptions == Prover.AXIOMS
        assert result2.conclusion == Formula('->', assumption2,
                                             Formula('->', assumption1,
                                                     proof.conclusion))
        assert result2.is_valid()
        
def test_prove_by_way_of_contradiction(debug=False):
    # Test on a simple nontautological proof
    prover = Prover(['Ax[x=c]', 'Ax[~x=c]'], debug)
    step1 = prover.add_assumption('Ax[x=c]')
    step2 = prover.add_universal_instantiation('x=c', step1, 'x')
    step3 = prover.add_assumption('Ax[~x=c]')
    step4 = prover.add_universal_instantiation('~x=c', step3, 'x')
    step5 = prover.add_tautological_implication('(z=z&~z=z)', {step2, step4})
    proof = prover.qed()
    if (debug):
        print("Testing prove_by_way_of_contradiction with assumption 'Ax[~x=c]'"
              ' for the following proof:\n' + str(proof))
    result = prove_by_way_of_contradiction(proof, Formula.parse('Ax[~x=c]'))
    assert result.assumptions == Prover.AXIOMS.union(
        {Schema(Formula.parse('Ax[x=c]'))})
    assert str(result.conclusion) == '~Ax[~x=c]'
    assert result.is_valid()

    if (debug):
        print("Testing prove_by_way_of_contradiction with assumption 'Ax[x=c]' "
              'for the following proof:\n' + str(proof))
    result = prove_by_way_of_contradiction(proof, Formula.parse('Ax[x=c]'))
    assert result.assumptions == Prover.AXIOMS.union(
        {Schema(Formula.parse('Ax[~x=c]'))})
    assert str(result.conclusion) == '~Ax[x=c]'
    assert result.is_valid()

    # Test on Russell's Paradox proof, when replacing the Axiom Schema of
    # Comprehension with its instance that is actually used.
    from predicates.some_proofs import \
         COMPREHENSION_AXIOM, prove_russell_paradox
    from predicates.some_proofs_test import test_prove_russell_paradox
    test_prove_russell_paradox()
    assumption = Formula.parse(
        'Ey[Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]]')
    proof = prove_russell_paradox()
    assert COMPREHENSION_AXIOM in proof.assumptions
    new_lines = []
    for line in proof.lines:
        if isinstance(line, Proof.AssumptionLine) and \
           line.assumption == COMPREHENSION_AXIOM:
            assert line.formula == assumption, \
                   'Unexpected instance of COMPREHENSION_AXIOM found in proof' \
                   " of Russell's Paradox. Cannot test " \
                   'prove_by_way_of_contradiction'
            new_lines.append(Proof.AssumptionLine(assumption,
                                                  Schema(assumption), {}))
        else:
            new_lines.append(line)
    new_assumptions = proof.assumptions.union({Schema(assumption)}) - \
                      {COMPREHENSION_AXIOM}
    new_proof = Proof(new_assumptions, proof.conclusion, new_lines)
    assert new_proof.is_valid()

    if debug:
        print("Testing prove_by_way_of_contradiction with assumption '" +
              str(assumption) + "' for the following proof:\n" + str(new_proof))
    result = prove_by_way_of_contradiction(new_proof, assumption)
    assert result.assumptions == Prover.AXIOMS
    assert str(result.conclusion) == \
           '~Ey[Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]]'
    assert result.is_valid()

def test_ex11(debug=False):
    test_remove_assumption(debug)
    test_prove_by_way_of_contradiction(debug)

def test_all(debug=False):
    test_ex11(debug)
