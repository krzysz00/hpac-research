# Stubs for matchpy.matching.code_generation (Python 3.6)
#
# NOTE: This dynamically typed stub was automatically generated by stubgen.

from ..expressions.constraints import CustomConstraint
from ..expressions.expressions import AssociativeOperation, SymbolWildcard, Wildcard
from ..expressions.functions import get_variables, op_iter
from ..utils import get_short_lambda_source
from .many_to_one import _EPS
from .syntactic import OPERATION_END, is_operation
from typing import Any

COLLAPSE_IF_RE: Any

class CodeGenerator:
    def __init__(self, matcher) -> None: ...
    def indent(self): ...
    def dedent(self): ...
    def add_line(self, line): ...
    def get_var_name(self, prefix): ...
    def generate_code(self, func_name: str = ..., add_imports: bool = ...): ...
    def final_label(self, index, subst_name): ...
    def generate_state_code(self, state): ...
    def commutative_var_entry(self, entry): ...
    def commutative_patterns(self, patterns): ...
    def generate_transition_code(self, transition): ...
    def get_args(self, operation, operation_type): ...
    def push_subjects(self, value, operation): ...
    def push_subst(self): ...
    def enter_eps(self, _): ...
    def exit_eps(self, _): ...
    def enter_operation(self, operation): ...
    def operation_symbol(self, operation): ...
    def exit_operation(self, value): ...
    def enter_symbol_wildcard(self, wildcard): ...
    def symbol_type(self, symbol): ...
    def exit_symbol_wildcard(self, value): ...
    def enter_fixed_wildcard(self, wildcard): ...
    def exit_fixed_wildcard(self, value): ...
    def enter_variable_assignment(self, variable_name, value): ...
    def enter_subst(self, subst): ...
    def expr(self, expr): ...
    def exit_subst(self, subst): ...
    def exit_variable_assignment(self): ...
    def enter_optional_wildcard(self, wildcard, variable_name): ...
    def optional_expr(self, expr): ...
    def exit_optional_wildcard(self, value): ...
    def enter_symbol(self, symbol): ...
    def symbol_repr(self, symbol): ...
    def exit_symbol(self, value): ...
    def enter_operation_end(self, _): ...
    def exit_operation_end(self, value): ...
    def enter_sequence_wildcard(self, wildcard): ...
    def create_operation(self, operation, operation_type, args): ...
    def exit_sequence_wildcard(self, value): ...
    def yield_final_substitution(self, pattern_index): ...
    def generate_constraints(self, constraints, transitions): ...
    def enter_global_constraint(self, constraint): ...
    def constraint_repr(self, constraint): ...
    def exit_global_constraint(self, constraint_index): ...
    def clean_code(self, code): ...
