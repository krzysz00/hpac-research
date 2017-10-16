# Stubs for matchpy.expressions.functions (Python 3.6)
#
# NOTE: This dynamically typed stub was automatically generated by stubgen.

from .expressions import Expression
from typing import Any, Dict, Optional

def is_constant(expression): ...
def is_syntactic(expression): ...
def get_head(expression): ...
def match_head(subject, pattern): ...
def preorder_iter(expression): ...
def preorder_iter_with_position(expression): ...
def is_anonymous(expression): ...
def contains_variables_from_set(expression, variables): ...
def get_variables(expression, variables: Optional[Any] = ...): ...
def rename_variables(expression: Expression, renaming: Dict[str, str]) -> Expression: ...
def register_operation_factory(operation, factory): ...
def register_operation_iterator(operation, iterator: Any = ..., length: Any = ...): ...
def create_operation_expression(old_operation, new_operands, variable_name: bool = ...): ...
def op_iter(operation): ...
def op_len(operation): ...
