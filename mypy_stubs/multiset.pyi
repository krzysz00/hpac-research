# Stubs for multiset (Python 3.6)
#
# NOTE: This dynamically typed stub was automatically generated by stubgen.

from typing import (Any, Optional, TypeVar, AbstractSet, Union,
                   ItemsView, KeysView, ValuesView, Generic, Iterable, Iterator)

T = TypeVar('T')
U = TypeVar('U')
class BaseMultiset(AbstractSet[T], Generic[T]):
    def __init__(self, iterable: Optional[Iterable[T]] = ...) -> None: ...
    def __new__(cls, iterable: Optional[Iterable[T]] = ...): ...
    def __contains__(self, element: object) -> bool: ...
    def __getitem__(self, element: T) -> int: ...
    def __len__(self) -> int: ...
    def __bool__(self) -> bool: ...
    def __iter__(self) -> Iterator[T]: ...
    def isdisjoint(self, other: AbstractSet[Any]) -> bool: ...
    def difference(self, *others: Iterable[T]) -> BaseMultiset[T]: ...
    def __sub__(self, other: AbstractSet[Any]) -> BaseMultiset[T]: ...
    def union(self, *others: Iterable[T]) -> BaseMultiset[T]: ...
    def __or__(self, other: AbstractSet[U]) -> BaseMultiset[Union[T, U]]: ...
    __ror__: BaseMultiset[T] = ...
    def combine(self, *others: Iterable[T]) -> BaseMultiset[T]: ...
    def __add__(self, other: AbstractSet[T]) -> BaseMultiset[T]: ...
    __radd__: AbstractSet[T] = ...
    def intersection(self, *others: Iterable[T]) -> BaseMultiset[T]: ...
    def __and__(self, other: AbstractSet[Any]) -> BaseMultiset[T]: ...
    __rand__: AbstractSet[T] = ...
    def symmetric_difference(self, other: Iterable[T]) -> BaseMultiset[T]: ...
    def __xor__(self, other: AbstractSet[U]) -> BaseMultiset[Union[T, U]]: ...
    __rxor__: AbstractSet[T] = ...
    def times(self, factor: int) -> BaseMultiset[T]: ...
    def __mul__(self, factor: int) -> BaseMultiset[T]: ...
    __rmul__: int = ...
    def issubset(self, other: Iterable[T]) -> bool: ...
    def __le__(self, other: AbstractSet[Any]) -> bool: ...
    def __lt__(self, other: AbstractSet[Any]) -> bool: ...
    def issuperset(self, other: Iterable[Any]) -> bool: ...
    def __ge__(self, other: AbstractSet[Any]) -> bool: ...
    def __gt__(self, other: AbstractSet[Any]) -> bool: ...
    def __eq__(self, other: object) -> bool: ...
    def __ne__(self, other: object) -> bool: ...
    def get(self, element: T, default: Optional[int]) -> Optional[int]: ...
    @classmethod
    def from_elements(cls, elements: Iterable[T], multiplicity: int) -> Multiset[T]: ...
    def copy(self) -> Multiset[T]: ...
    __copy__: Multiset[T] = ...
    def items(self) -> ItemsView[T, int]: ...
    def distinct_elements(self) -> KeysView[T]: ...
    def multiplicities(self) -> ValuesView[int]: ...

class Multiset(BaseMultiset[T]):
    def __setitem__(self, element: T, multiplicity: int): ...
    def __delitem__(self, element: T): ...
    def update(self, *others: Iterable[T]) -> None: ...
    def union_update(self, *others: Iterable[T]) -> None: ...
    def __ior__(self, other: AbstractSet[U]) -> Multiset[Union[T, U]]: ...
    def intersection_update(self, *others: Iterable[Any]) -> None: ...
    def __iand__(self, other: AbstractSet[Any]) -> Multiset[T]: ...
    def difference_update(self, *others: Iterable[Any]) -> None: ...
    def __isub__(self, other: AbstractSet[Any]) -> Multiset[T]: ...
    def symmetric_difference_update(self, other: Iterable[Any]) -> None: ...
    def __ixor__(self, other: AbstractSet[U]) -> Multiset[Union[T, U]]: ...
    def times_update(self, factor: int) -> None: ...
    def __imul__(self, factor: int) -> Multiset[T]: ...
    def add(self, element: T, multiplicity: int = ...) -> None: ...
    def remove(self, element: T, multiplicity: Optional[int] = ...) -> int: ...
    def discard(self, element: T, multiplicity: Optional[int] = ...) -> int: ...
    def pop(self, element: T, default: int) -> int: ...
    def setdefault(self, element: T, default: int) -> int: ...
    def clear(self) -> None: ...

class FrozenMultiset(BaseMultiset):
    def __hash__(self): ...
