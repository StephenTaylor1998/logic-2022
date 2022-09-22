# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/syntax.py

"""Syntactic handling of propositional formulas."""

from __future__ import annotations
from functools import lru_cache
from typing import Mapping, Optional, Set, Tuple, Union

from logic_utils import frozen, memoized_parameterless_method


@lru_cache(maxsize=100)  # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= 'p' and string[0] <= 'z' and \
           (len(string) == 1 or string[1:].isdecimal())


@lru_cache(maxsize=100)  # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return string == 'T' or string == 'F'


@lru_cache(maxsize=100)  # Cache the return value of is_unary
def is_unary(string: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return string == '~'


@lru_cache(maxsize=100)  # Cache the return value of is_binary
def is_binary(string: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    return string == '&' or string == '|' or string == '->'
    # For Chapter 3:
    # return string in {'&', '|',  '->', '+', '<->', '-&', '-|'}


@frozen
class Formula:
    """An immutable propositional formula in tree representation, composed from
    variable names, and operators applied to them.

    Attributes:
        root (`str`): the constant, variable name, or operator at the root of
            the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand of the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand of the
            root, if the root is a binary operator.
    """
    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None):
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand for the root, if the root is a unary or
                binary operator.
            second: the second operand for the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert first is not None and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root)
            assert first is not None and second is not None
            self.root, self.first, self.second = root, first, second

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 1.1
        if is_variable(self.root) or is_constant(self.root):
            return f"{self.root}"
        elif is_unary(self.root):
            return f"{self.root}{self.first}"
        else:
            return f"({self.first}{self.root}{self.second})"

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        # Task 1.2
        var_set = set()
        if is_variable(self.root):
            var_set.add(self.root)
        elif is_constant(self.root):
            pass
        elif is_unary(self.root):
            var_set = var_set | Formula.variables(self.first)
        else:
            var_set = var_set | Formula.variables(self.first)
            var_set = var_set | Formula.variables(self.second)

        return var_set

    @memoized_parameterless_method
    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        # Task 1.3
        op_set = set()
        if is_variable(self.root):
            pass
        elif is_constant(self.root):
            op_set.add(self.root)
        elif is_unary(self.root):
            op_set.add(self.root)
            op_set = op_set | Formula.operators(self.first)
        else:
            op_set.add(self.root)
            op_set = op_set | Formula.operators(self.first)
            op_set = op_set | Formula.operators(self.second)
        return op_set

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a variable name (e.g.,
            ``'x12'``) or a unary operator followed by a variable name, then the
            parsed prefix will include that entire variable name (and not just a
            part of it, such as ``'x1'``). If no prefix of the given string is a
            valid standard string representation of a formula then returned pair
            should be of ``None`` and an error message, where the error message
            is a string with some human-readable content.
        """

        # Task 1.4

        if string == '':
            return None, ''

        def get_variable(_s: str, _front, _end):
            while front < len(_s) and _end <= len(_s):
                if is_variable(string[_front:_end]):
                    _end += 1
                    continue
                else:
                    break

            return Formula(_s[_front:_end - 1]), _end - 2, _end - 1

        def get_binary(_s: str, _front, _end):
            while front < len(_s) and _end <= len(_s):
                if is_binary(string[_front:_end]) or string[_front:_end] in ['-']:
                    _end += 1
                    continue
                else:
                    break

            if is_binary(string[_front:_end - 1]):
                return _s[_front:_end - 1], _end - 2, _end - 1

            return None, _end - 1, _end

        stack = []
        front, end = 0, 1
        while front < len(string) and end <= len(string):

            # variable
            if is_variable(string[front:end]):
                variable, front, end = get_variable(string, front, end)
                while stack and stack[-1] == '~':
                    variable = Formula(stack.pop(), variable)

                stack.append(variable)

            # constant
            elif is_constant(string[front:end]):
                constant = Formula(string[front:end])
                while stack and stack[-1] == '~':
                    constant = Formula(stack.pop(), constant)

                stack.append(constant)

            # operator
            elif is_unary(string[front:end]):
                stack.append(string[front:end])

            elif string[front:end] in ['&', '|', '-']:
                binary, front, end = get_binary(string, front, end)
                stack.append(binary)

            # left brackets
            elif string[front:end] == '(':
                stack.append(string[front:end])

            # right brackets
            elif string[front:end] == ')':
                if not stack:
                    return None, ''
                if len(stack) < 4:
                    end -= 1
                    break

                f2 = stack.pop()  # formula 2
                op = stack.pop()  # operator
                f1 = stack.pop()  # formula 1
                lb = stack.pop()  # left brackets '('
                if not (isinstance(f1, Formula) and isinstance(f2, Formula) and is_binary(op) and lb == '('):
                    return None, ''

                formula = Formula(op, f1, f2)
                while stack and stack[-1] == '~':
                    formula = Formula(stack.pop(), formula)

                stack.append(formula)
            else:
                end -= 1
                break

            front += 1
            end += 1

        if not stack:
            return None, ''

        if isinstance(stack[0], Formula):

            if len(stack) == 1:
                return stack[0], string[end:]

            else:
                remain = ''
                for item in stack[1:]:
                    remain += str(item)

                remain = remain + string[end:]
                return stack[0], str(remain)

        else:
            return None, ''

    @staticmethod
    def is_formula(string: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            string: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        # Task 1.5
        formula, remain = Formula._parse_prefix(string)
        if isinstance(formula, Formula) and remain == '':
            return True
        else:
            return False

    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(string)
        # Task 1.6
        formula, _ = Formula._parse_prefix(string)
        return formula

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        # Optional Task 1.7

    @staticmethod
    def parse_polish(string: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8

    def substitute_variables(self, substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Substitutes in the current formula, each variable name `v` that is a
        key in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            variable name occurrences originating in the current formula are
            substituted (i.e., variable name occurrences originating in one of
            the specified substitutions are not subjected to additional
            substitutions).

        Examples:
            >>> Formula.parse('((p->p)|r)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)'), 'r': Formula.parse('p')})
            (((q&r)->(q&r))|p)
        """
        for variable in substitution_map:
            assert is_variable(variable)
        # Task 3.3

    def substitute_operators(self, substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            operator occurrences originating in the current formula are
            substituted (i.e., operator occurrences originating in one of the
            specified substitutions are not subjected to additional
            substitutions).

        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_constant(operator) or is_unary(operator) or \
                   is_binary(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        # Task 3.4
