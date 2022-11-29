# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Sequence, Union

from logic_utils import frozendict

from propositions.syntax import *
from propositions.semantics import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction import *


def formulas_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulas that capture the given model: ``'``\ `x`\ ``'``
    for each variable name `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable name `x` that is assigned
    the value ``False``.

    Parameters:
        model: model to construct the formulas for.

    Returns:
        A list of the constructed formulas, ordered alphabetically by variable
        name.

    Examples:
        >>> formulas_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    # Task 6.1a
    return [Formula(variable) if model[variable] else Formula('~', Formula(variable)) for variable in sorted(model)]


def prove_in_model(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulas
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulas to prove.

    Returns:
        If `formula` evaluates to ``True`` in the given model, then a valid
        proof of `formula`; otherwise a valid proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulas that capture the given model, in
        the order returned by `formulas_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        >>> proof = prove_in_model(Formula.parse('(p->q7)'),
        ...                        {'q7': False, 'p': False})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (p->q7)
        >>> proof.statement.assumptions
        (~p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True

        >>> proof = prove_in_model(Formula.parse('(p->q7)'),
        ...                        {'q7': False, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        ~(p->q7)
        >>> proof.statement.assumptions
        (p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)

    # Task 6.1b
    def update_line_number(line, num):
        if line.rule:
            return Proof.Line(line.formula, line.rule, [index + num for index in line.assumptions])
        else:
            return line

    def update_all_lines_number(lines, num):
        return [update_line_number(line, num) for line in lines]

    if formula.root == "->":
        # p->q
        if evaluate(formula, model):
            # p->q == true
            if evaluate(formula.first, model):
                # p == true --> q == true
                proof = prove_in_model(formula.second, model)  # proof q
                origin_lines = list(proof.lines)
                origin_lines.append(Proof.Line(Formula("->", formula.second, formula), I1, []))  # q->(p->q)
                origin_lines.append(
                    Proof.Line(formula, MP, [len(origin_lines) - 2, len(origin_lines) - 1]))  # (p->q)
                return Proof(
                    InferenceRule(formulas_capturing_model(model), formula),
                    AXIOMATIC_SYSTEM,
                    origin_lines
                )

            else:
                # p == false --> q == True or False
                proof = prove_in_model(formula.first, model)  # proof ~p
                origin_lines = list(proof.lines)
                origin_lines.append(
                    Proof.Line(Formula("->", Formula("~", formula.first), formula), I2, [])  # ~p->(p->q)
                )
                origin_lines.append(
                    Proof.Line(formula, MP, [len(origin_lines) - 2, len(origin_lines) - 1])  # (p->q)
                )
                return Proof(
                    InferenceRule(formulas_capturing_model(model), formula),
                    AXIOMATIC_SYSTEM,
                    origin_lines
                )

        else:
            # p->q == false --> (p == true and q == false)
            proof_p = prove_in_model(formula.first, model)  # proof p
            proof_not_q = prove_in_model(formula.second, model)  # proof ~q
            origin_lines = list()
            new_lines1 = list(proof_p.lines)
            new_lines2 = update_all_lines_number(list(proof_not_q.lines), len(new_lines1))
            origin_lines.extend(new_lines1)
            origin_lines.extend(new_lines2)
            not_P_Q = Formula("~", formula)  # ~(p->q)
            not_Q_not_P_Q = Formula("->", Formula("~", formula.second), not_P_Q)  # ~q->~(p->q)
            P_not_Q_not_P_Q = Formula("->", formula.first, not_Q_not_P_Q)  # p->(~q->~(p->q))

            origin_lines.append(Proof.Line(P_not_Q_not_P_Q, NI, []))  # ~q->~(p->q)
            origin_lines.append(
                Proof.Line(not_Q_not_P_Q, MP, [len(new_lines1) - 1, len(origin_lines) - 1]))  # ~(p->q)
            origin_lines.append(
                Proof.Line(not_P_Q, MP, [len(new_lines1) + len(new_lines2) - 1, len(origin_lines) - 1])  # ~(p->q)
            )
            return Proof(
                InferenceRule(formulas_capturing_model(model), not_P_Q),
                AXIOMATIC_SYSTEM,
                origin_lines
            )

    else:
        # p or ~p
        if formula.root == "~":
            # ~p
            if evaluate(formula, model):
                # ~p == true --> p == false
                return prove_in_model(formula.first, model)
            else:
                # ~p == false --> ~~p == True
                proof = prove_in_model(formula.first, model)
                origin_lines = list(proof.lines)
                not_not_P = Formula("~", formula)  # ~~p
                origin_lines.append(Proof.Line(Formula("->", formula.first, not_not_P), NN, []))  # p->~~p
                origin_lines.append(
                    Proof.Line(not_not_P, MP, [len(origin_lines) - 2, len(origin_lines) - 1]))  # ~~p
                return Proof(
                    InferenceRule(formulas_capturing_model(model), not_not_P),
                    AXIOMATIC_SYSTEM,
                    origin_lines
                )
        else:
            if evaluate(formula, model):
                # p == True
                origin_lines = [Proof.Line(formula)]
                return Proof(
                    InferenceRule(formulas_capturing_model(model), formula),
                    AXIOMATIC_SYSTEM,
                    origin_lines
                )
            else:
                # p == False
                origin_lines = [Proof.Line(Formula("~", formula))]
                return Proof(
                    InferenceRule(formulas_capturing_model(model), Formula("~", formula)),
                    AXIOMATIC_SYSTEM,
                    origin_lines
                )


def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
    """Combines the two given proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_from_negation: valid proof of `conclusion` from the same
            assumptions and inference rules of `proof_from_affirmation`, but
            with the last assumption being ``'~``\ `assumption`\ ``'`` instead
            of `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If `proof_from_affirmation` is of ``['p', '~q', 'r'] ==> '(p&(r|~r))'``,
        then `proof_from_negation` must be of
        ``['p', '~q', '~r'] ==> '(p&(r|~r))'`` and the returned proof is of
        ``['p', '~q'] ==> '(p&(r|~r))'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules

    # Task 6.2

    def update_line_number(line, num):
        if line.rule:
            return Proof.Line(line.formula, line.rule, [index + num for index in line.assumptions])
        else:
            return line

    def update_all_lines_number(_lines, num):
        return [update_line_number(line, num) for line in _lines]

    pos_proof = remove_assumption(proof_from_affirmation)
    neg_proof = remove_assumption(proof_from_negation)
    index_pos = len(pos_proof.lines) - 1
    index_neg = len(pos_proof.lines) + len(neg_proof.lines) - 1

    not_p_q_q = Formula("->", neg_proof.statement.conclusion, neg_proof.statement.conclusion.second)
    p_q_not_p_q_q = Formula("->", pos_proof.statement.conclusion, not_p_q_q)

    # (p->q)->((~p->q)->q)
    # ((~p->q)->q)
    # q
    r_line = Proof.Line(p_q_not_p_q_q, R, [])
    mp1_line = Proof.Line(not_p_q_q, MP, [index_pos, index_neg + 1])
    mp2_line = Proof.Line(neg_proof.statement.conclusion.second, MP, [index_neg, index_neg + 2])

    # process statement
    statement = InferenceRule(pos_proof.statement.assumptions, neg_proof.statement.conclusion.second)

    # process lines
    lines_neg = update_all_lines_number(list(neg_proof.lines), len(pos_proof.lines))
    lines = [*pos_proof.lines, *lines_neg, r_line, mp1_line, mp2_line]
    # proof
    new_proof = Proof(statement, pos_proof.rules, lines)
    return new_proof


def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulas that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variable names of `tautology`, from whose
            formulas to prove.

    Returns:
        A valid proof of the given tautology from the formulas that capture the
        given model, in the order returned by
        `formulas_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        >>> proof = prove_tautology(Formula.parse('(~(p->p)->q)'),
        ...                         {'p': True, 'q': False})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (~(p->p)->q)
        >>> proof.statement.assumptions
        (p, ~q)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True

        >>> proof = prove_tautology(Formula.parse('(~(p->p)->q)'))
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (~(p->p)->q)
        >>> proof.statement.assumptions
        ()
        >>> proof.rules == AXIOMATIC_SYSTEM
        True
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())

    # Task 6.3a

    def update_model(origin_model: Model, variable: str, value: bool) -> Model:
        new_dict = {variable: value}
        new_dict.update(origin_model)
        return new_dict

    other_variable = [variable for variable in Formula.variables(tautology) if variable not in model]
    other_variable = sorted(other_variable)

    if len(other_variable) == 0:
        # finally program will stop here
        return prove_in_model(tautology, model)
    else:
        pos_model = update_model(model, other_variable[0], True)
        neg_model = update_model(model, other_variable[0], False)
        pos_proof = prove_tautology(tautology, pos_model)
        neg_proof = prove_tautology(tautology, neg_model)
        return reduce_assumption(pos_proof, neg_proof)


def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})
    # Task 6.3b
    variable_set = Formula.variables(formula)
    assert len(variable_set) != 0, '[INFO] formula should contain variables.'

    model_list = all_models(variable_set)  # list of models
    for model in model_list:
        if not evaluate(formula, model):
            return model
    return prove_tautology(formula, {})


def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))

        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    # Task 6.4a


def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion contain no
            constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in {rule.conclusion}.union(rule.assumptions):
        assert formula.operators().issubset({'->', '~'})
    # Task 6.4b


def model_or_inconsistency(formulas: Sequence[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulas hold, or proves
    ``'~(p->p)'`` from these formulas.

    Parameters:
        formulas: formulas that use only the operators ``'->'`` and ``'~'``, to
            either find a model of, or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulas hold if such exists,
        otherwise a valid proof of ``'~(p->p)'`` from the given formulas via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulas:
        assert formula.operators().issubset({'->', '~'})
    # Task 6.5


def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulas
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'`` (and may contain constants), whose affirmation
            or negation is to prove.
        model: model from whose formulas to prove.

    Returns:
        If `formula` evaluates to ``True`` in the given model, then a valid
        proof of `formula`; otherwise a valid proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulas that capture the given model, in
        the order returned by `formulas_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.

    Examples:
        >>> proof = prove_in_model_full(Formula.parse('(p&q7)'),
        ...                             {'q7': True, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (p&q7)
        >>> proof.statement.assumptions
        (p, q7)
        >>> proof.rules == AXIOMATIC_SYSTEM_FULL
        True

        >>> proof = prove_in_model_full(Formula.parse('(p&q7)'),
        ...                             {'q7': False, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        ~(p&q7)
        >>> proof.statement.assumptions
        (p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM_FULL
        True
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    # Optional Task 6.6
