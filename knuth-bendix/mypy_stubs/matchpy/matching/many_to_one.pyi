# Stubs for matchpy.matching.many_to_one (Python 3.6)
#
# NOTE: This dynamically typed stub was automatically generated by stubgen.

from .. import functions
from ..expressions.expressions import Expression, Operation, Pattern, Symbol
from ..expressions.substitution import Substitution
from multiset import Multiset
from typing import Any, Dict, Iterable, Iterator, Optional, Sequence, Tuple, Type, Union, Generic, TypeVar, List
from graphviz import Digraph, Graph

LabelType = Union[Expression, Type[Operation]]
HeadType = Optional[Union[Expression, Type[Operation], Type[Symbol]]]
MultisetOfInt = Multiset[int]
MultisetOfExpression = Multiset[Expression]

_T = TypeVar('_T')
class ManyToOneMatcher(Generic[_T]):
    rename: bool = ...
    def __init__(self, *patterns: Expression, rename: bool=...) -> None: ...
    def add(self, pattern: Pattern, label: _T=...) -> None: ...
    def match(self, subject: Expression) -> Iterator[Tuple[_T, Substitution]]: ...
    def is_match(self, subject: Expression) -> bool: ...
    @classmethod
    def _collect_variable_renaming(cls, expression: Expression, position: Optional[List[int]]=...,
                                   variables: Optional[Dict[str, str]]=...) -> Dict[str, str]: ...
    def as_graph(self) -> Digraph: ...

class ManyToOneReplacer:
    matcher: ManyToOneMatcher[functions.ReplacementRule] = ...
    def __init__(self, *rules: functions.ReplacementRule) -> None: ...
    def add(self, rule: functions.ReplacementRule) -> None: ...
    def replace(self, expression: Expression, max_count: int=...) -> Union[Expression, Sequence[Expression]]: ...
    def replace_post_order(self, expression: Expression) -> Union[Expression, Sequence[Expression]]: ...
