from matchpy import (Expression, Substitution, get_head, Operation, Symbol)
from matchpy import substitute as _substitute

from typing import TypeVar, Set, Tuple, Optional, Union, cast, Type, List


_T = TypeVar('_T')
PartialOrder = Set[Tuple[_T, _T]]


def transitive_closure(order: PartialOrder[_T]) -> PartialOrder[_T]:
    """Take a partial ordering and return its transitive closure

    :param ordering: The ordering to close
    :returns: Transitive closure of :ref:`ordering`"""
    while True:
        new_relations = set((x, w) for x, y in order
                            for q, w in order if q == y)
        new_order = order | new_relations
        if order == new_order:
            return order
        order = new_order


def substitute(term: Expression, substitution: Substitution) -> Expression:
    """Wrapper around :fn:`matchpy.substitute` that does a typecheck"""
    ret = _substitute(term, substitution)
    if not isinstance(ret, Expression):
        raise(ValueError("Unexpected list of expressions", ret, "from",
                         substitution, "on", term))
    return ret


Operator = Union[Symbol, Type[Operation]]
"""Either a function or a constant symbol"""


def to_operator(term: Expression) -> Optional[Operator]:
    """Perform any necessary extraction and type casting to make
    :ref:`term' into a :ref:`Operator`"""
    if isinstance(term, Operation):
        return cast(Type[Operation], get_head(term))
    elif isinstance(term, Symbol):
        return term
    else:
        return None


def operands(term: Expression) -> Optional[List[Expression]]:
    """Return the operands of the outer layer of the given term, if any.

    :returns: For variables, returns None.
    For constants, returns [] (empty list)
    For functions, returns the list of operands"""
    if not to_operator(term):
        return None
    elif isinstance(term, Operation):
        return term.operands
    elif isinstance(term, Symbol):
        return []
    else:
        raise(TypeError("We should have covered all the cases"))
