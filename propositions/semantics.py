# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""
import time
from typing import AbstractSet, Iterable, Iterator, Mapping, Sequence, Tuple

from propositions.syntax import *
from propositions.proofs import *

#: A model for propositional-logic formulas, a mapping from variable names to
#: truth values.
Model = Mapping[str, bool]


def is_model(model: Model) -> bool:
    """Checks if the given dictionary is a model over some set of variable
    names.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variable
        names, ``False`` otherwise.
    """
    for key in model:
        if not is_variable(key):
            return False
    return True


def variables(model: Model) -> AbstractSet[str]:
    """Finds all variable names over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variable names over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()


def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variable names of the
            given formula, to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.

    Examples:
        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': False})
        True

        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': True})
        False
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))

    # Task 2.1
    if is_variable(formula.root):
        return model[formula.root]

    if formula.root == 'T':
        return True

    if formula.root == 'F':
        return False

    if formula.root == '~':
        return not evaluate(formula.first, model)

    if formula.root == '&':
        return evaluate(formula.first, model) and evaluate(formula.second, model)

    if formula.root == '|':
        return evaluate(formula.first, model) or evaluate(formula.second, model)

    if formula.root == '->':
        return (not evaluate(formula.first, model)) or evaluate(formula.second, model)


def all_models(variables: Sequence[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variable names.

    Parameters:
        variables: variable names over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variable names. The
        order of the models is lexicographic according to the order of the given
        variable names, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]

        >>> list(all_models(['q', 'p']))
        [{'q': False, 'p': False}, {'q': False, 'p': True}, {'q': True, 'p': False}, {'q': True, 'p': True}]
    """
    for v in variables:
        assert is_variable(v)
    # Task 2.2
    list1 = [{}]

    for variable in variables:
        list2 = []
        for item in list1:
            new_item = item.copy()
            new_item[variable] = False
            list2.append(new_item)
            new_item = item.copy()
            new_item[variable] = True
            list2.append(new_item)

        list1 = list2

    return list1


def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    models.

    Parameters:
        formula: formula to calculate the truth value of.
        models: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.

    Examples:
        >>> list(truth_values(Formula.parse('~(p&q76)'), all_models(['p', 'q76'])))
        [True, True, True, False]
    """
    # Task 2.3
    return [evaluate(formula, model) for model in models]


def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Task 2.4

    variable = Formula.variables(formula)
    variable_list = sorted(list(variable))
    str_len_list = [len(variable) for variable in variable_list]
    models = all_models(variable_list)

    # [to-do: optimize code]
    # print(*[f"| {variable} " for variable in variable_list], '| ', formula, ' |', sep='')
    # print(*[f"|{'-' * (str_len + 2)}" for str_len in str_len_list], f"|{'-' * (len(str(formula))+2)}|", sep='')
    # for model in models:
    #     print(*[f"| {'T' if model[variable] else 'F'}{' ' * str_len}"
    #             for variable, str_len in zip(variable_list, str_len_list)],
    #           '| ', 'T' if evaluate(formula, model) else 'F', ' '*(len(str(formula))), '|', sep='')

    # [modified]
    print(''.join([f"| {variable} " for variable in variable_list]),
          f"| {formula} |", sep='')
    print(''.join([f"|{'-' * (str_len + 2)}" for str_len in str_len_list]),
          f"|{'-' * (len(str(formula)) + 2)}|", sep='')

    for model in models:
        table_body = ''.join([
            f"| {'T' if model[variable] else 'F'}{' ' * str_len}"
            for variable, str_len in zip(variable_list, str_len_list)
        ]) + f"| {'T' if evaluate(formula, model) else 'F'}{' ' * (len(str(formula)))}|\n"
        print(table_body, end='')

    # [demo]
    # variable_list = sorted(list(Formula.variables(formula)))
    # models = all_models(variable_list)
    # variable_list.append(str(formula))
    # widths = [len(variable) for variable in variable_list]
    #
    # print('|', *[f" {variable} |" for variable in variable_list], sep='')
    # print('|', *[f"{'-' * (width + 2)}|" for width in widths], sep='')
    # for model in models:
    #     values = [model[variable] for variable in variable_list[:-1]]
    #     values.append(evaluate(formula, model))
    #     print('|', *[f" {'T' if value else 'F'}{' ' * width}|" for value, width in zip(values, widths)], sep='')


def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    # Task 2.5a
    truth_list = truth_values(formula, all_models(Formula.variables(formula)))
    if False in truth_list:
        return False
    else:
        return True


def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Task 2.5b
    truth_list = truth_values(formula, all_models(Formula.variables(formula)))
    if True in truth_list:
        return False
    else:
        return True


def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # Task 2.5c
    truth_list = truth_values(formula, all_models(Formula.variables(formula)))
    if True in truth_list:
        return True
    else:
        return False


def _synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single conjunctive
    clause that evaluates to ``True`` in the given model, and to ``False`` in
    any other model over the same variable names.

    Parameters:
        model: model over a nonempty set of variable names, in which the
            synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """

    assert is_model(model)
    assert len(model.keys()) > 0
    # Task 2.6
    variable_list = sorted([variable for variable in model])
    formula = Formula(variable_list[0]) if model[variable_list[0]] else Formula('~', Formula(variable_list[0]))
    for variable in variable_list[1:]:
        formula = Formula('&', formula, Formula(variable) if model[variable] else Formula('~', Formula(variable)))

    return formula


def synthesize(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variable names,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variable names for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variable names, in the order returned
            by `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Task 2.7
    models = [model for model, truth in zip(all_models(variables), values) if truth]
    if not models:
        return Formula("&", Formula(variables[0]), Formula("~", Formula(variables[0])))

    formula = _synthesize_for_model(models[0])
    for model in models:
        formula = Formula('|', formula, _synthesize_for_model(model))

    return formula


def _synthesize_for_all_except_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single disjunctive
    clause that evaluates to ``False`` in the given model, and to ``True`` in
    any other model over the same variable names.

    Parameters:
        model: model over a nonempty set of variable names, in which the
            synthesized formula is to not hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Optional Task 2.8
    variable_list = sorted([variable for variable in model])
    formula = Formula('~', Formula(variable_list[0])) if model[variable_list[0]] else Formula(variable_list[0])
    for variable in variable_list[1:]:
        formula = Formula('|', formula, Formula('~', Formula(variable)) if model[variable] else Formula(variable))

    return formula


def synthesize_cnf(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in CNF over the given variable names,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variable names for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variable names, in the order returned
            by `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize_cnf(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Optional Task 2.9
    models = [model for model, truth in zip(all_models(variables), values) if not truth]
    if not models:
        return Formula("|", Formula(variables[0]), Formula("~", Formula(variables[0])))

    formula = _synthesize_for_all_except_model(models[0])
    for model in models:
        formula = Formula('&', formula, _synthesize_for_all_except_model(model))

    return formula


def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.

    Examples:
        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': True, 'q': False})
        False

        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': False, 'q': False})
        True
    """
    assert is_model(model)
    # Task 4.2

    conclusion = evaluate(rule.conclusion, model)
    for assumption in rule.assumptions:
        conclusion |= (not evaluate(assumption, model))

    return conclusion


def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3
    variables_set = rule.variables()
    models = all_models(list(variables_set))
    for model in models:
        if not evaluate_inference(rule, model):
            return False

    return True
