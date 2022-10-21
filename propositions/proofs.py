# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/proofs.py

"""Proofs by deduction in Propositional Logic."""

from __future__ import annotations
from typing import AbstractSet, FrozenSet, List, Mapping, Optional, Sequence, \
    Set, Tuple, Union

from logic_utils import frozen, memoized_parameterless_method

from propositions.syntax import *

#: A mapping from variable names to formulas.
SpecializationMap = Mapping[str, Formula]


@frozen
class InferenceRule:
    """An immutable inference rule in Propositional Logic, comprised of zero
    or more assumed propositional formulas, and a conclusion propositional
    formula.

    Attributes:
        assumptions (`~typing.Tuple`\\[`~propositions.syntax.Formula`, ...]):
            the assumptions of the rule.
        conclusion (`~propositions.syntax.Formula`): the conclusion of the rule.
    """
    assumptions: Tuple[Formula, ...]
    conclusion: Formula

    def __init__(self, assumptions: Sequence[Formula], conclusion: Formula):
        """Initializes an `InferenceRule` from its assumptions and conclusion.

        Parameters:
            assumptions: the assumptions for the rule.
            conclusion: the conclusion for the rule.
        """
        self.assumptions = tuple(assumptions)
        self.conclusion = conclusion

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes a string representation of the current inference rule.

        Returns:
            A string representation of the current inference rule.
        """
        return str([str(assumption) for assumption in self.assumptions]) + \
               ' ==> ' + "'" + str(self.conclusion) + "'"

    def __eq__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is an `InferenceRule` object that
            equals the current inference rule, ``False`` otherwise.
        """
        return isinstance(other, InferenceRule) and \
               self.assumptions == other.assumptions and \
               self.conclusion == other.conclusion

    def __ne__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not an `InferenceRule` object or
            does not does not equal the current inference rule, ``False``
            otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    def variables(self) -> Set[str]:
        """Finds all variable names in the current inference rule.

        Returns:
            A set of all variable names used in the assumptions and in the
            conclusion of the current inference rule.
        """
        # Task 4.1
        variable_set = set()
        for formula in self.assumptions:
            variable_set.update(Formula.variables(formula))

        variable_set.update(Formula.variables(self.conclusion))

        return variable_set

    def specialize(self, specialization_map: SpecializationMap) -> \
            InferenceRule:
        """Specializes the current inference rule by simultaneously substituting
        each variable name `v` that is a key in `specialization_map` with the
        formula `specialization_map[v]`.

        Parameters:
            specialization_map: mapping defining the specialization to be
                performed.

        Returns:
            The resulting inference rule.
        """
        for variable in specialization_map:
            assert is_variable(variable)
        # Task 4.4
        conclusion = Formula.substitute_variables(self.conclusion, specialization_map)
        assumptions = [
            Formula.substitute_variables(assumption, specialization_map)
            for assumption in self.assumptions
        ]
        return InferenceRule(assumptions, conclusion)

    @staticmethod
    def _merge_specialization_maps(
            specialization_map1: Union[SpecializationMap, None],
            specialization_map2: Union[SpecializationMap, None]) -> \
            Union[SpecializationMap, None]:
        """Merges the given specialization maps while checking their
        consistency.

        Parameters:
            specialization_map1: first mapping to merge, or ``None``.
            specialization_map2: second mapping to merge, or ``None``.

        Returns:
            A single mapping containing all (key, value) pairs that appear in
            either of the given maps, or ``None`` if one of the given maps is
            ``None`` or if some key appears in both given maps but with
            different values.
        """
        if specialization_map1 is not None:
            for variable in specialization_map1:
                assert is_variable(variable)
        if specialization_map2 is not None:
            for variable in specialization_map2:
                assert is_variable(variable)
        # Task 4.5a

        # check None
        if specialization_map1 is None:
            return None
        if specialization_map2 is None:
            return None

        # check duplicate
        for variable in specialization_map1:
            if variable in specialization_map2.keys():
                if specialization_map2[variable] != specialization_map1[variable]:
                    return None

        # merge
        specialization_set = {}
        specialization_set.update(specialization_map1)
        specialization_set.update(specialization_map2)
        return specialization_set

    @staticmethod
    def _formula_specialization_map(general: Formula, specialization: Formula) \
            -> Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the given formula
        specializes to the given specialization.

        Parameters:
            general: non-specialized formula for which to compute the map.
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of `general`.
        """

        # Task 4.5b

        # <---------------------------recursion--------------------------->
        def recursion(f1: Formula, f2: Formula, specialization_map: SpecializationMap) \
                -> Union[SpecializationMap, None]:

            if is_variable(f1.root):
                specialization_map = InferenceRule._merge_specialization_maps(
                    specialization_map, {f1.root: f2})
                return specialization_map

            if is_constant(f1.root):
                if is_constant(f2.root) and f1.root == f2.root:
                    return specialization_map
                else:
                    return None

            if is_unary(f1.root) and is_unary(f2.root):
                return recursion(f1.first, f2.first, specialization_map)

            if is_binary(f1.root) and is_binary(f2.root):
                if f1.root != f2.root:
                    return None
                specialization_map = InferenceRule._merge_specialization_maps(
                    recursion(f1.first, f2.first, specialization_map),
                    recursion(f1.second, f2.second, specialization_map)
                )
                return specialization_map

            return None

        # <---------------------------recursion--------------------------->

        specialization_dict = recursion(general, specialization, dict())
        return specialization_dict

    def specialization_map(self, specialization: InferenceRule) -> \
            Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the current
        inference rule specializes to the given specialization.

        Parameters:
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of the current rule.
        """
        # Task 4.5c
        if len(self.assumptions) != len(specialization.assumptions):
            return None

        specialization_map = InferenceRule._formula_specialization_map(
            self.conclusion, specialization.conclusion)

        for assumption_g, assumption_s in zip(self.assumptions, specialization.assumptions):
            specialization_map = InferenceRule._merge_specialization_maps(
                specialization_map,
                InferenceRule._formula_specialization_map(assumption_g, assumption_s)
            )

        return specialization_map

    def is_specialization_of(self, general: InferenceRule) -> bool:
        """Checks if the current inference rule is a specialization of the given
        inference rule.

        Parameters:
            general: non-specialized inference rule to check.

        Returns:
            ``True`` if the current inference rule is a specialization of
            `general`, ``False`` otherwise.
        """
        return general.specialization_map(self) is not None


@frozen
class Proof:
    """An immutable deductive proof in Propositional Logic, comprised of a
    statement in the form of an inference rule, a set of inference rules that
    may be used in the proof, and a list of lines that prove the statement via
    these inference rules.

    Attributes:
        statement (`InferenceRule`): the statement proven by the proof.
        rules (`~typing.AbstractSet`\\[`InferenceRule`]): the allowed rules of
            the proof.
        lines (`~typing.Tuple`\\[`Line`]): the lines of the proof.
    """
    statement: InferenceRule
    rules: FrozenSet[InferenceRule]
    lines: Tuple[Proof.Line, ...]

    def __init__(self, statement: InferenceRule,
                 rules: AbstractSet[InferenceRule],
                 lines: Sequence[Proof.Line]):
        """Initializes a `Proof` from its statement, allowed inference rules,
        and lines.

        Parameters:
            statement: the statement to be proven by the proof.
            rules: the allowed rules for the proof.
            lines: the lines for the proof.
        """
        self.statement = statement
        self.rules = frozenset(rules)
        self.lines = tuple(lines)

    @frozen
    class Line:
        """An immutable line in a deductive proof, comprised of a formula that
        is justified either as an assumption of the proof, or as the conclusion
        of a specialization of an allowed inference rule of the proof, the
        assumptions of which are justified by previous lines in the proof.

        Attributes:
            formula (`~propositions.syntax.Formula`): the formula justified by
                the line.
            rule (`~typing.Optional`\\[`InferenceRule`]): the inference rule,
                out of those allowed in the proof, that has a specialization
                that concludes the formula; or ``None`` if the formula is
                justified as an assumption of the proof.
            assumptions (`~typing.Optional`\\[`~typing.Tuple`\\[`int`]): tuple
                of zero or more numbers of previous lines in the proof whose
                formulas are the respective assumptions of the specialization of
                the rule that concludes the formula, if the formula is not
                justified as an assumption of the proof.
        """
        formula: Formula
        rule: Optional[InferenceRule]
        assumptions: Optional[Tuple[int, ...]]

        def __init__(self, formula: Formula,
                     rule: Optional[InferenceRule] = None,
                     assumptions: Optional[Sequence[int]] = None):
            """Initializes a `~Proof.Line` from its formula, and optionally its
            rule and numbers of justifying previous lines.

            Parameters:
                formula: the formula to be justified by the line.
                rule: the inference rule, out of those allowed in the proof,
                    that has a specialization that concludes the formula; or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
                assumptions: numbers of previous lines in the proof whose
                    formulas are the respective assumptions of the
                    specialization of the rule that concludes the formula, or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
            """
            assert (rule is None and assumptions is None) or \
                   (rule is not None and assumptions is not None)
            self.formula = formula
            self.rule = rule
            if assumptions is not None:
                self.assumptions = tuple(assumptions)

        def __repr__(self) -> str:
            """Computes a string representation of the current line.

            Returns:
                A string representation of the current line.
            """
            if self.rule is None:
                return str(self.formula)
            else:
                r = str(self.formula) + '    (Inference Rule ' + str(self.rule)
                if len(self.assumptions) == 1:
                    r += ' on line ' + str(self.assumptions[0])
                elif len(self.assumptions) > 1:
                    r += ' on lines ' + ','.join(map(str, self.assumptions))
                r += ')'
                return r

        def is_assumption(self) -> bool:
            """Checks if the current proof line is justified as an assumption of
            the proof.

            Returns:
                ``True`` if the current proof line is justified as an assumption
                of the proof, ``False`` otherwise.
            """
            return self.rule is None

    def __repr__(self) -> str:
        """Computes a string representation of the current proof.

        Returns:
            A string representation of the current proof.
        """
        r = 'Proof of ' + str(self.statement) + ' via inference rules:\n'
        for rule in self.rules:
            r += '  ' + str(rule) + '\n'
        r += 'Lines:\n'
        for i in range(len(self.lines)):
            r += ('%3d) ' % i) + str(self.lines[i]) + '\n'
        r += "QED\n"
        return r

    def rule_for_line(self, line_number: int) -> Union[InferenceRule, None]:
        """Computes the inference rule whose conclusion is the formula justified
        by the specified line, and whose assumptions are the formulas justified
        by the lines specified as the assumptions of that line.

        Parameters:
            line_number: number of the line according to which to compute the
                inference rule.

        Returns:
            The computed inference rule, with assumptions ordered in the order
            of their numbers in the specified line, or ``None`` if the specified
            line is justified as an assumption.
        """
        assert line_number < len(self.lines)
        # Task 4.6a

        if line_number == 0:
            return None

        return InferenceRule(
            [self.lines[index].formula for index in self.lines[line_number].assumptions],
            self.lines[line_number].formula
        )

    def is_line_valid(self, line_number: int) -> bool:
        """Checks if the specified line validly follows from its justifications.

        Parameters:
            line_number: number of the line to check.

        Returns:
            If the specified line is justified as an assumption, then ``True``
            if the formula justified by this line is an assumption of the
            current proof, ``False`` otherwise. Otherwise (i.e., if the
            specified line is justified as a conclusion of an inference rule),
            ``True`` if the rule specified for that line is one of the allowed
            inference rules in the current proof, and it has a specialization
            that satisfies all of the following:

            1. The conclusion of that specialization is the formula justified by
               that line.
            2. The assumptions of this specialization are the formulas justified
               by the lines that are specified as the assumptions of that line
               (in the order of their numbers in that line), all of which must
               be previous lines.
        """
        assert line_number < len(self.lines)
        # Task 4.6b

        this_line = self.lines[line_number]

        if len(self.rules) == 0:
            return False

        if this_line.is_assumption():
            if this_line.formula not in self.statement.assumptions:
                return False
            return True

        if this_line.rule not in self.rules:
            # print(f"[{this_line.rule}] [{self.rules}] [{this_line.rule not in self.rules}]")
            return False

        if this_line.formula != self.statement.conclusion and line_number == len(self.lines) - 1:
            return False

        for i in this_line.assumptions:
            if line_number <= i:
                return False

        rule = InferenceRule([self.lines[i].formula for i in this_line.assumptions], this_line.formula)
        return rule.is_specialization_of(this_line.rule)

    def is_valid(self) -> bool:
        """Checks if the current proof is a valid proof of its claimed statement
        via its inference rules.

        Returns:
            ``True`` if the current proof is a valid proof of its claimed
            statement via its inference rules, ``False`` otherwise.
        """
        # Task 4.6c

        if len(self.lines) == 0:
            return False

        flag = True
        for line_number in range(len(self.lines)):
            flag = self.is_line_valid(line_number) and flag

        return flag


def prove_specialization(proof: Proof, specialization: InferenceRule) -> Proof:
    """Converts the given proof of an inference rule to a proof of the given
    specialization of that inference rule.

    Parameters:
        proof: valid proof to convert.
        specialization: specialization of the rule proven by the given proof.

    Returns:
        A valid proof of the given specialization via the same inference rules
        as the given proof.
    """
    assert proof.is_valid()
    assert specialization.is_specialization_of(proof.statement)
    # Task 5.1
    specialization_map = proof.statement.specialization_map(specialization)
    statement = specialization
    rules = proof.rules
    lines = [Proof.Line(
        Formula.substitute_variables(line.formula, specialization_map),
        line.rule,
        line.assumptions if hasattr(line, "assumptions") else None
    ) for line in proof.lines]
    return Proof(statement, rules, lines)


def _inline_proof_once(main_proof: Proof, line_number: int,
                       lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating the usage of (a specialization of)
    that "lemma" rule in the specified line in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        line_number: number of the line in `main_proof` that should be replaced.
        lemma_proof: valid proof of the inference rule of the specified line (an
            allowed inference rule of `main_proof`).

    Returns:
        A valid proof obtained by replacing the specified line in `main_proof`
        with a full (specialized) list of lines proving the formula of the
        specified line from the lines specified as the assumptions of that line,
        and updating justification line numbers specified throughout the proof
        to maintain the validity of the proof. The set of allowed inference
        rules in the returned proof is the union of the rules allowed in the two
        given proofs, but the "lemma" rule that is used in the specified line in
        `main_proof` is no longer used in the corresponding lines in the
        returned proof (and thus, this "lemma" rule is used one less time in the
        returned proof than in `main_proof`).
    """
    assert main_proof.is_valid()
    assert line_number < len(main_proof.lines)
    assert main_proof.lines[line_number].rule == lemma_proof.statement
    assert lemma_proof.is_valid()
    # Task 5.2a
    specialization = main_proof.rule_for_line(line_number)
    special_lemma_proof = prove_specialization(lemma_proof, specialization)

    line_map = dict()
    lemma_lines = []
    delete_lines = []
    for special_lemma_line_number, special_lemma_line in enumerate(special_lemma_proof.lines):
        # print(special_lemma_line.formula)
        lemma_formula = special_lemma_line.formula
        main_assumptions = specialization.assumptions
        # record the map between "line assumptions" and "line-index of main_proof.lines"
        if lemma_formula in main_assumptions:
            index = main_assumptions.index(lemma_formula)
            # print("index: ", index)
            line_map[special_lemma_line_number] = main_proof.lines[line_number].assumptions[index]
            delete_lines.append(special_lemma_line_number)
            continue

        lemma_assumptions = []
        for assumption_index in special_lemma_line.assumptions:
            if assumption_index in line_map:
                lemma_assumptions.append(line_map[assumption_index])
            else:
                count_delete = 0
                for l in delete_lines:
                    if l < assumption_index:
                        count_delete += 1
                lemma_assumptions.append(assumption_index + line_number - count_delete)

        lemma_lines.append(Proof.Line(special_lemma_line.formula, special_lemma_line.rule, lemma_assumptions))

    rest_main_lines = []
    for main_line in main_proof.lines[line_number+1:]:
        main_assumptions = []
        for assumption_index in main_line.assumptions:
            if assumption_index < line_number:
                main_assumptions.append(assumption_index)
            else:
                main_assumptions.append(assumption_index + len(lemma_lines) - 1)
        rest_main_lines.append(Proof.Line(main_line.formula, main_line.rule, main_assumptions))

    lines = (*main_proof.lines[:line_number], *lemma_lines, *rest_main_lines)

    return Proof(main_proof.statement, main_proof.rules.union(lemma_proof.rules), lines)


def inline_proof(main_proof: Proof, lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating all usages of (any specializations
    of) that "lemma" rule in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        lemma_proof: valid proof of one of the allowed inference rules of
            `main_proof`.

    Returns:
        A valid proof obtained from `main_proof` by inlining (an appropriate
        specialization of) `lemma_proof` in lieu of each line that specifies the
        "lemma" inference rule proved by `lemma_proof` as its justification. The
        set of allowed inference rules in the returned proof is the union of the
        rules allowed in the two given proofs but without the "lemma" rule
        proved by `lemma_proof`.
    """
    assert main_proof.is_valid()
    assert lemma_proof.is_valid()
    # Task 5.2b

    def get_line_number(_main_proof, _lemma_proof) -> int:
        lemma_rule = _lemma_proof.statement
        for index, line in enumerate(_main_proof.lines):
            if line.rule is None:
                continue

            if lemma_rule.is_specialization_of(line.rule):
                # print("is rules")
                return index
        return -1

    while True:
        line_number = get_line_number(main_proof, lemma_proof)
        if line_number == -1:
            break
        else:
            main_proof = _inline_proof_once(main_proof, line_number, lemma_proof)
    print(main_proof)

    return Proof(main_proof.statement, main_proof.rules - {lemma_proof.statement}, main_proof.lines)
