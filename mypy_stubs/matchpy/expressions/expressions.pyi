# Stubs for matchpy.expressions.expressions (Python 3.6)
#
# NOTE: This dynamically typed stub was automatically generated by stubgen.

from . import constraints
from abc import ABCMeta
from multiset import Multiset
from typing import (Any, List, Tuple, Type, Union, overload,
                    Optional, Callable, Iterator, NamedTuple)


__all__ = [
    'Expression', 'Arity', 'Atom', 'Symbol', 'Wildcard', 'Operation', 'SymbolWildcard', 'Pattern', 'make_dot_variable',
    'make_plus_variable', 'make_star_variable', 'make_symbol_variable', 'AssociativeOperation', 'CommutativeOperation',
    'OneIdentityOperation'
]

MultisetOfStr = Multiset[str]
MultisetOfVariables = Multiset['Wildcard']

ExprPredicate = Optional[Callable[['Expression'], bool]]
ExpressionsWithPos = Iterator[Tuple['Expression', Tuple[int, ...]]]

class Expression:
    variable_name: Optional[str] = ...
    def __init__(self, variable_name) -> None: ...
    variables: MultisetOfVariables = ...
    def collect_variables(self, variables: MultisetOfVariables) -> None: ...
    symbols:  MultisetOfStr = ...
    def collect_symbols(self, symbols: MultisetOfStr) -> None: ...
    def is_constant(self) -> bool: ...
    def is_syntactic(self) -> bool: ...
    def with_renamed_vars(self, renaming: Any) -> Type[Expression]: ...
    def preorder_iter(self, predicate: ExprPredicate=...) -> ExpressionsWithPos: ...
    def __getitem__(self, position: Union[Tuple[int, ...], slice]) -> Type[Expression]: ...
    def __contains__(self, expression: Expression) -> bool: ...
    def __hash__(self): ...

_ArityBase = NamedTuple('_ArityBase', [('min_count', int), ('fixed_size', bool)])
class Arity(_ArityBase):
    nullary: Arity
    unary: Arity
    binary: Arity
    ternary: Arity
    polyadic: Arity
    variadic: Arity
    ...

class _OperationMeta(ABCMeta):
    def __init__(cls, name, bases, dct) -> None: ...
    def __call__(cls, *operands: Expression, variable_name: Optional[str]=...) -> Type[Expression]: ...  # type: ignore

class Operation(Expression):
    name: str = ...
    arity: Arity = ...
    associative: bool = ...
    commutative: bool = ...
    one_identity: bool = ...
    infix: bool = ...
    operands: List[Expression] = ...
    def __init__(self, *operands: Expression, variable_name: Optional[str]=...) -> None: ...
    @staticmethod
    def new(name: str, arity: Arity, class_name: str=..., *, associative: bool=..., commutative: bool=..., one_identity: bool=..., infix: bool=...) -> Type[Operation]: ...
    def __lt__(self, other): ...
    def __eq__(self, other): ...
    def __iter__(self) -> Optional[Iterator[Expression]]: ...
    def __len__(self) -> int: ...
    def __getitem__(self, key: Union[Tuple[int, ...], slice]) -> Type[Expression]: ...
    def __contains__(self, expression: Expression) -> bool: ...
    def collect_variables(self, variables: MultisetOfVariables) -> None: ...
    def collect_symbols(self, symbols: MultisetOfStr) -> None: ...
    def __hash__(self): ...
    def with_renamed_vars(self, renaming: Any) -> Type[Operation]: ...
    def __copy__(self) -> Operation: ...

class AssociativeOperation:
    @classmethod
    def __subclasshook__(cls, C): ...

class CommutativeOperation:
    @classmethod
    def __subclasshook__(cls, C): ...

class OneIdentityOperation:
    @classmethod
    def __subclasshook__(cls, C): ...

class Atom(Expression):
    __iter__: Any = ...

class Symbol(Atom):
    name: Any = ...
    head: Any = ...
    def __init__(self, name: str, variable_name: Optional[str]=...) -> None: ...
    def collect_symbols(self, symbols: MultisetOfStr) -> None: ...
    def with_renamed_vars(self, renaming: Any) -> Type[Symbol]: ...
    def __copy__(self) -> Symbol: ...
    def __lt__(self, other): ...
    def __eq__(self, other): ...
    def __hash__(self): ...

class Wildcard(Atom):
    head: Any = ...
    min_count: int = ...
    fixed_size: bool = ...
    optional: Any = ...
    def __init__(self, min_count: int, fixed_size: bool, variable_name: Optional[str]=..., optional: Type[Expression]=...) -> None: ...
    def with_renamed_vars(self, renaming: Any) -> Type[Wildcard]: ...
    @staticmethod
    def dot(name: Any=...) -> Wildcard: ...
    @staticmethod
    def optional(name: Optional[str], default: Type[Expression]) -> Wildcard: ...
    @staticmethod
    def symbol(name: str=..., symbol_type: Type[Symbol]=...) -> SymbolWildcard: ...
    @staticmethod
    def star(name: Optional[str]=...) -> Wildcard: ...
    @staticmethod
    def plus(name: Optional[str]=...) -> Wildcard: ...
    def __lt__(self, other): ...
    def __eq__(self, other): ...
    def __hash__(self): ...
    def __copy__(self) -> Wildcard: ...

class SymbolWildcard(Wildcard):
    symbol_type: Type[Symbol] = ...
    def __init__(self, symbol_type: Type[Symbol]=..., variable_name: Optional[str]=...) -> None: ...
    def with_renamed_vars(self, renaming: Any) -> Type[SymbolWildcard]: ...
    def __eq__(self, other): ...
    def __hash__(self): ...
    def __copy__(self) -> SymbolWildcard: ...

class Pattern:
    expression: Type[Expression] = ...
    constraints: List[Any] = ...
    def __init__(self, expression: Expression, *constraints: Any) -> None: ...
    def __eq__(self, other): ...
    @property
    def is_syntactic(self) -> bool: ...
    @property
    def local_constraints(self) -> bool: ...
    @property
    def global_constraints(self) -> bool: ...

def make_dot_variable(name: str) -> Wildcard: ...
def make_symbol_variable(name: str, symbol_type: Optional[Type[Symbol]] = ...) -> SymbolWildcard: ...
def make_star_variable(name: str) -> Wildcard: ...
def make_plus_variable(name: str) -> Wildcard: ...