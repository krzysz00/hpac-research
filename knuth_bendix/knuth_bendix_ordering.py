# -*- coding: utf-8 -*-
# knuth-bendix - Implementation of the Knuth-Bendix algorithm
# Copyright (C) 2017 Krzysztof Drewniak <krzysdrewniak@gmail.com>

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.
"""A class implementing the Knuth-Bendix ordering"""
from .unification import equal_mod_renaming
from .utils import (transitive_closure, PartialOrder,
                    Operator, to_operator)

from matchpy import (Expression,  Operation, Symbol)
from typing import (Mapping, Type, cast)


# This ordering is from
# Dick, Jeremy, John Kalmus, and Ursula Martin.
# “Automating the Knuth Bendix Ordering.”
# Acta Informatica 28.2 (1990): 95–119. Web.
class KnuthBendixOrdering(object):
    """Implement the Knuth-Bendix ordering for a set of operators.

    The ordering here requires the following information:

    1. A partial order >> on the operators
    (symbols in the rules, like "1" are 0-arity operators)
    2. Weights for all operators, which must be non-negative
    They must also satisfy the condition that, for a unary operator f
    with weight 0, we have f >> g for all g != f
    3. A weight for variables, w, such that, for all constants a, w(a) >= w."""

    def __init__(self, weights: Mapping[Operator, int], var_weight: int,
                 op_gt: PartialOrder[Operator]) -> None:
        """:param weights: Weights for all operations and constants.
        :param var_weight: Weight for variables,
        :param op_gt: Partial order (will be transitively closed over)
        on the operators. Send in >"""
        self.op_gt = transitive_closure(op_gt)
        self.arities = {}  # type: Mapping[Operator, int]
        for op in weights:
            if (op, op) in self.op_gt:
                raise ValueError(">> on operators is reflexive for some reason")  # NOQA
            if (isinstance(op, type) and issubclass(op, Operation)):
                op = cast(Type[Operation], op)
                if not op.arity.fixed_size:
                    raise ValueError("Fixed-arity functions only in Knuth-Bendix ordering")  # NOQA
                self.arities[op] = op.arity.min_count
                # The finicky condition
                if weights[op] == 0 and self.arities[op] == 1:
                    for op2 in weights:
                        if op != op2 and (op, op2) not in self.op_gt:
                            raise(ValueError("Unary operator {} with weight 0 failed its ordering requirement".format(op)))  # NOQA
            elif isinstance(op, Symbol):
                self.arities[op] = 0
                if weights[op] < var_weight:
                    raise ValueError("Improper weight for constant.")
            else:
                raise TypeError("Unexpected type in weights")
        self.weights = weights
        self.var_weight = var_weight

    def weight(self, term: Expression) -> int:
        """Calculate the weight of the given term under
        the Knuth-Bendix ordering"""
        ret = self.var_weight * sum(term.variables.multiplicities())
        for t, _ in term.preorder_iter():
            t_prime = to_operator(t)
            if t_prime in self.arities:
                ret += self.weights[t_prime]
        return ret

    def __call__(self, s: Expression, t: Expression) -> bool:
        """Determine whether s > t under the given Knuth-Bendix ordering"""
        # Fail if more of a variable on the right than on the left
        if not s.variables >= t.variables:
            return False
        w_s = self.weight(s)
        w_t = self.weight(t)
        if w_s > w_t:
            return True
        elif w_s == w_t:
            s_head = to_operator(s)
            t_head = to_operator(t)
            # The f(f(... f(x))) == x condition
            if s_head is not None and self.arities[s_head] == 1:
                s_prime = cast(Operation, s).operands[0]
                iterating = True
                while iterating:
                    new_head = to_operator(s_prime)
                    if new_head != s_head:
                        iterating = False
                    if equal_mod_renaming(s_prime, t):
                        return True
                    if isinstance(s_prime, Operation):
                        s_prime = s_prime.operands[0]
                    else:
                        iterating = False

            if s_head != t_head:
                return (s_head, t_head) in self.op_gt
            else:
                if s_head is None or isinstance(s_head, Symbol):
                    return False
                elif isinstance(s, Operation) and isinstance(t, Operation):
                    for i in range(0, self.arities[s_head]):
                        if equal_mod_renaming(s.operands[i], t.operands[i]):
                            continue
                        if self(s.operands[i], t.operands[i]):
                            return True
                        else:
                            return False
                else:
                    raise(TypeError("Ok, this is literally impossible. type(s_head) == {}, type(t_head) == {}".format(  # NOQA
                                    type(s_head), type(t_head))))
        return False
