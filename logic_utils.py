# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: logic_utils.py

"""Python infrastructure for the Mathematical Logic through Programming book."""

from functools import lru_cache, wraps
from typing import Any, Callable, Dict, Iterator, Set, Type, TypeVar, cast

T = TypeVar('T')

def frozen(cls: Type[T]) -> Type[T]:
    """A class decorator that disallows assignment to instance variables after
    construction.

    Parameters:
        cls: class to modify.

    Returns:
        The given class, modified so that assignment to instance variable is
        disallowed after construction.
    """
    original_init = cls.__init__
    original_setattr = cls.__setattr__
    original_delattr = cls.__delattr__
    mutable_ids: Set[int] = set()
    @wraps(cls.__setattr__)
    def setattr_wrapper(self, name, value):
        if id(self) in mutable_ids:
            original_setattr(self, name, value)
        else:
            raise Exception("Cannot assign to field '" + name +
                            "' of immutable class '" + cls.__name__ + "'")
    @wraps(cls.__delattr__)
    def delattr_wrapper(self, name, value):
        if id(self) in mutable_ids:
            original_delattr(self, name, value)
        else:
            raise Exception("Cannot delete field '" + name +
                            "' of immutable class '" + cls.__name__ + "'")
    @wraps(cls.__init__)
    def init_wrapper(self, *args, **kwargs):
        mutable_ids.add(id(self))
        original_init(self, *args, **kwargs)
        mutable_ids.remove(id(self))

    setattr(cls, '__setattr__', setattr_wrapper)
    setattr(cls, '__delattr__',  delattr_wrapper)
    setattr(cls, '__init__', init_wrapper)
    return cls

class frozendict(Dict[Any, Any]):
    """An immutable variant of the built-in `dict` class."""

    def __init__(self, *args, **kwargs):
        super().update(dict(*args, **kwargs))
        
    def update(self, *args, **kwargs):
        raise Exception('Cannot modify a frozendict')

    __delattr__ = __delitem__ = __setattr__ = __setitem__ = clear = pop = \
                  popitem = setdefault =  cast(Callable[..., Any], update)
S = TypeVar('S')

def memoized_parameterless_method(method: Callable[[T], S]) -> Callable[[T], S]:
    """A method decorator for parameterless methods of immutable classes that
    memoizes the return value to avoid recalculation.

    Parameters:
        method: method to modify.

    Returns:
        The given method, modified so that after its first execution, its
        functionality is replaced with simply returning the value calculated by
        its first execution. If the value calculated by the given method has a
        `copy`\ ``()`` method, then instead of returning this value, each
        execution of the returned method, including the first one, makes a fresh
        call to this `copy`\ ``()`` method and returns the result.
    """
    methodname = method.__name__
    @wraps(method)
    def wrapper(obj):
        value = method(obj)
        if hasattr(value, 'copy'):
            new_wrapper = lambda:value.copy()
        else:
            new_wrapper = lambda:value
        object.__setattr__(obj, methodname, wraps(method)(new_wrapper))
        return new_wrapper()
    return wrapper


class __prefix_with_index_sequence_generator:
    """ A generator for a sequence of the form 'z1', 'z2', 'z3', ..., where the
    prefix 'z' is customizable. """

    def __init__(self, prefix: str) -> None:
        self.__prefix = prefix
        self.__counter = 0

    def __iter__(self) -> Iterator[str]:
        return self

    def __next__(self) -> str:
        self.__counter = self.__counter + 1
        return self.__prefix + str(self.__counter)

    def _reset_for_test(self) -> None:
        """ Reset this generator. For use by tests only """
        self.__counter = 0

#: A generator for fresh variable names. The first call to
#: `next`\ ``(``\ `fresh_variable_name_generator`\ ``)`` will return ``'z1'``,
#: the second call to `next`\ ``(``\ `fresh_variable_name_generator`\ ``)`` will
#: return ``'z2'``, and so on.
fresh_variable_name_generator: Iterator[str] = \
    __prefix_with_index_sequence_generator('z')

#: A generator for fresh constant names. The first call to
#: `next`\ ``(``\ `fresh_constant_name_generator`\ ``)`` will return ``'e1'``,
#: the second call to `next`\ ``(``\ `fresh_constant_name_generator`\ ``)`` will
#: return ``'e2'``, and so on.
fresh_constant_name_generator: Iterator[str] = \
    __prefix_with_index_sequence_generator('e')

@lru_cache(maxsize=100) # Cache the return value of is_z_and_number
def is_z_and_number(string: str) -> bool:
    """Checks if the given string is ``z`` followed by a number.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is ``z`` followed by a number, ``False``
        otherwise.
    """
    return  string[0] == 'z' and string[1:].isdecimal()
