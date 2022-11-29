# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *


def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` to a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    # Task 5.3a


def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulas `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `double_conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
                    Formula('->', antecedent2_proof.statement.conclusion, consequent))
    ).is_specialization_of(double_conditional)
    # Task 5.3b


def remove_assumption(proof: Proof) -> Proof:
    """Converts the given proof of some `conclusion` formula, the last
    assumption of which is an assumption `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4
    # make new statement for the new proof
    assumptions = proof.statement.assumptions[:-1]
    A = proof.statement.assumptions[-1]  # assumption A
    statement = InferenceRule(assumptions, Formula("->", A, proof.statement.conclusion))
    conclusion_of_axioms = [rule.conclusion for rule in proof.rules if rule != MP]
    # process the assumption 'A' in original proof with four cases
    modified_lines = list()
    line_index = -1
    for line in proof.lines:

        # case 1&2: B is an axiom of L, or B is a member of Γ
        if line.rule != MP:
            in_assumption_or_axiom = line.formula in assumptions or line.formula in conclusion_of_axioms
            in_rules = (line.rule is not None) and (line.rule in proof.rules)

            if in_assumption_or_axiom or in_rules:
                A_B = Formula("->", A, line.formula)      # (A → B)
                B_A_B = Formula("->", line.formula, A_B)  # (B → (A → B))
                modified_lines.append(line)                                                   # B
                modified_lines.append(Proof.Line(B_A_B, I1, []))                              # (B → (A → B))
                modified_lines.append(Proof.Line(A_B, MP, [line_index + 1, line_index + 2]))  # (A → B)
                line_index += 3
                continue

        # case 3: B is A
        if line.formula == A:
            modified_lines.append(Proof.Line(Formula("->", A, A), I0, []))
            line_index += 1
            continue

        # case 4: B is deduced from two previous steps
        # (1)
        # ......
        # (k)     (A → C)                                  (deduction from Γ)
        # ......
        # (l)     (A → (C → B))                            (deduction from Γ)
        # (l + 1) ((A → (C → B)) → ((A → C) → (A → B)))    (L2)
        # (l + 2) ((A → C) → (A → B))                      (l + 1, l + 2, MP)
        # (l + 3) (A → B)                                  (k, l + 2, MP)
        else:
            # Now, line.rule == MP and line.formula != current_assumption
            # get B and C from origin MP line
            C = proof.lines[line.assumptions[0]].formula  # C
            C_B = proof.lines[line.assumptions[1]].formula  # (C → B)
            B = C_B.second  # B

            # pre-process formula
            A_B = Formula("->", A, B)                      # (A → B)
            A_C = Formula("->", A, C)                      # (A → C)
            A_C_A_B = Formula("->", A_C, A_B)              # ((A→C)→(A→B))
            A_C_B = Formula("->", A, C_B)                  # (A → (C → B))
            A_C_B_A_C_A_B = Formula("->", A_C_B, A_C_A_B)  # ((A → (C → B)) → ((A → C) → (A → B)))

            # find index of (A → (C → B)) and (A → C)
            index_of_A_C_B = -1  # (A → (C → B))
            index_of_A_C = -1  # (A → C)
            for index in range(len(modified_lines)):
                if modified_lines[index].formula == A_C_B:
                    index_of_A_C_B = index
                if modified_lines[index].formula == A_C:
                    index_of_A_C = index

            # (A->(C->B))->((A->C)->(A->B))
            modified_lines.append(Proof.Line(A_C_B_A_C_A_B, D, []))
            # (A->C)->(A->B)
            modified_lines.append(Proof.Line(A_C_A_B, MP, [index_of_A_C_B, line_index + 1]))
            # (A->B)
            modified_lines.append(Proof.Line(A_B, MP, [index_of_A_C, line_index + 2]))
            line_index += 3

    # update rules
    rules = {MP, I0, I1, D}
    rules.update(proof.rules)
    return Proof(statement, rules, modified_lines)


def prove_from_opposites(proof_of_affirmation: Proof,
                         proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.
        conclusion: formula to prove.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6

    def update_line_number(line, num):
        if line.rule:
            return Proof.Line(line.formula, line.rule, [index + num for index in line.assumptions])
        else:
            return line

    def update_all_lines_number(_lines, num):
        return [update_line_number(line, num) for line in _lines]

    # collect statement from affirmation and negation
    pos_assumptions = proof_of_affirmation.statement.assumptions
    neg_assumptions = [
        assumption for assumption in proof_of_negation.statement.assumptions if assumption not in pos_assumptions
    ]
    assumptions = [*pos_assumptions, *neg_assumptions]
    statement = InferenceRule(assumptions, conclusion)

    # process lines
    neg_lines = update_all_lines_number(proof_of_negation.lines, len(proof_of_affirmation.lines))
    lines = list(proof_of_affirmation.lines) + neg_lines
    p_index = len(proof_of_affirmation.lines) - 1
    not_p_index = len(lines) - 1

    # process rules
    rules = set()
    rules.update(proof_of_affirmation.rules)
    rules.update(proof_of_negation.rules)
    rules.update({MP, I2})

    # now we use (~p->(p->q)) to find q
    p = proof_of_affirmation.statement.conclusion   # p
    not_p = proof_of_negation.statement.conclusion  # ~p
    p_q = Formula("->", p, conclusion)              # (p->q)
    not_p_p_q = Formula("->", not_p, p_q)           # (~p->(p->q))

    lines.append(Proof.Line(not_p_p_q, I2, []))                           # (~p->(p->q))
    lines.append(Proof.Line(p_q, MP, [not_p_index, not_p_index + 1]))     # (p->q)
    lines.append(Proof.Line(conclusion, MP, [p_index, not_p_index + 2]))  # q

    return Proof(statement, rules, lines)


def prove_by_way_of_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, to a proof of `formula` from the
    same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7
    proof_remove_assumption = remove_assumption(proof)

    # ~q
    # q
    # (~q->~(p->p))
    # ((~q->~(p->p))->((p->p)->q))
    # ((p->p)->q)
    not_q = proof_remove_assumption.statement.conclusion.first
    q = not_q.first
    not_q_not_p_p = Formula("->", not_q, Formula('~', Formula.parse('(p->p)')))
    not_q_not_p_p_p_p_q = Formula("->", not_q_not_p_p, Formula("->", Formula.parse('(p->p)'), q))
    p_p_q = Formula("->", Formula.parse('(p->p)'), q)

    lines = list(proof_remove_assumption.lines)
    lines.append(Proof.Line(not_q_not_p_p_p_p_q, N, []))                   # ((~q->~(p->p))->((p->p)->q))
    lines.append(Proof.Line(p_p_q, MP, [len(lines) - 2, len(lines) - 1]))  # ((p->p)->q)
    lines.append(Proof.Line(Formula.parse('(p->p)'), I0, []))              # (p->p)
    lines.append(Proof.Line(q, MP, [len(lines) - 1, len(lines) - 2]))      # q

    # pack the new info
    statement = InferenceRule(proof_remove_assumption.statement.assumptions, q)

    rules = {N}
    rules.update(proof_remove_assumption.rules)

    return Proof(statement, rules, lines)
