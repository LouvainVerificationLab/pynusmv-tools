"""

The mucalculus package defines mu-calculus models, formulas, adequate
explanations and generates adequate explanations.

The package is structured as follows:

    - model.py defines mu-calculus models and provides a way to build such a
      model from the currently read model;
    - formula.py defines the different mu-calculus operators; each operator
      defines its own evaluation and explanation functions;
    - explanation.py defines the structure of adequate explanations for the
      mu-calculus. These explanations are produced by explain functions of
      mu-calculus operators.
"""

from copy import deepcopy
from collections import Mapping, MutableSet
from pynusmv.exception import PyNuSMVError

class MuCalculusError(PyNuSMVError):
    """Generic mu-calculus package error."""
    pass

class MuCalculusModelError(MuCalculusError):
    """Model-related errors."""
    pass

class UnknownTransitionError(MuCalculusError):
    """Unknown transition name."""
    pass

class UnknownVariableError(MuCalculusError):
    """Variable not in context."""
    pass

class CannotExplainFalseError(MuCalculusError):
    """Trying to explain why state belongs to false."""
    pass

class TranslationError(MuCalculusError):
    """Cannot translate model or formula."""
    pass

class ChoiceError(MuCalculusError):
    """A choice is incorrect."""
    pass

class ExclusiveChoiceError(ChoiceError):
    """The choice must be exclusive but was not."""
    pass


class hashabledict(Mapping):
    """
    Hashable read-only dictionary.
    
    Inspired from frozendict https://pypi.python.org/pypi/frozendict/.
    """

    def __init__(self, *args, **kwargs):
        self.__dict = dict(*args, **kwargs)
        self.__hash = None

    def __getitem__(self, key):
        return self.__dict[key]

    def copy(self):
        return hashabledict(self)

    def __iter__(self):
        return iter(self.__dict)

    def __len__(self):
        return len(self.__dict)

    def __repr__(self):
        return '<hashabledict %s>' % repr(self.__dict)

    def __hash__(self):
        if self.__hash is None:
            self.__hash = hash(frozenset(self.__dict.items()))
        return self.__hash


class orderedset(MutableSet):
    """
    Ordered set. A classic set that remembers order of insertion.
    """

    def __init__(self, iterable=None):
        self.__set = set()
        self.__list = list()
        if iterable is not None:
            for e in iterable:
                self.add(e)

    def __contains__(self, element):
        return element in self.__set

    def __iter__(self):
        return iter(self.__list)

    def __len__(self):
        return len(self.__set)

    def add(self, element):
        if element not in self.__set:
            self.__set.add(element)
            self.__list.append(element)

    def discard(self, element):
        if element in self.__set:
            self.__set.discard(element)
            self.__list.remove(element)

    def __repr__(self):
        return '<orderedset {%s}>' % ", ".join(str(elem) for elem in self)