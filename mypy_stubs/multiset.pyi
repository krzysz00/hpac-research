# Stubs for multiset (Python 3.6)
#
# NOTE: This dynamically typed stub was automatically generated by stubgen.

from typing import Any, Optional

_int_type = int

class BaseMultiset:
    def __init__(self, iterable: Optional[Any] = ...) -> None: ...
    def __new__(cls, iterable: Optional[Any] = ...): ...
    def __contains__(self, element): ...
    def __getitem__(self, element): ...
    def __len__(self): ...
    def __bool__(self): ...
    def __iter__(self): ...
    def isdisjoint(self, other): ...
    def difference(self, *others): ...
    def __sub__(self, other): ...
    def union(self, *others): ...
    def __or__(self, other): ...
    __ror__: Any = ...
    def combine(self, *others): ...
    def __add__(self, other): ...
    __radd__: Any = ...
    def intersection(self, *others): ...
    def __and__(self, other): ...
    __rand__: Any = ...
    def symmetric_difference(self, other): ...
    def __xor__(self, other): ...
    __rxor__: Any = ...
    def times(self, factor): ...
    def __mul__(self, factor): ...
    __rmul__: Any = ...
    def issubset(self, other): ...
    def __le__(self, other): ...
    def __lt__(self, other): ...
    def issuperset(self, other): ...
    def __ge__(self, other): ...
    def __gt__(self, other): ...
    def __eq__(self, other): ...
    def __ne__(self, other): ...
    def get(self, element, default): ...
    @classmethod
    def from_elements(cls, elements, multiplicity): ...
    def copy(self): ...
    __copy__: Any = ...
    def items(self): ...
    def distinct_elements(self): ...
    def multiplicities(self): ...

class Multiset(BaseMultiset):
    def __setitem__(self, element, multiplicity): ...
    def __delitem__(self, element): ...
    def update(self, *others): ...
    def union_update(self, *others): ...
    def __ior__(self, other): ...
    def intersection_update(self, *others): ...
    def __iand__(self, other): ...
    def difference_update(self, *others): ...
    def __isub__(self, other): ...
    def symmetric_difference_update(self, other): ...
    def __ixor__(self, other): ...
    def times_update(self, factor): ...
    def __imul__(self, factor): ...
    def add(self, element, multiplicity: int = ...): ...
    def remove(self, element, multiplicity: Optional[Any] = ...): ...
    def discard(self, element, multiplicity: Optional[Any] = ...): ...
    def pop(self, element, default): ...
    def setdefault(self, element, default): ...
    def clear(self): ...

class FrozenMultiset(BaseMultiset):
    def __hash__(self): ...
