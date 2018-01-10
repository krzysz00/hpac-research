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
"""A class implementing the lexicographic path ordering"""
from .utils import (transitive_closure, PartialOrder,
                    Operator, to_operator, operands)

from matchpy import (Expression)
from typing import List


class LexPathOrdering(object):
    """Implement the lexicographic path ordering for given operators.

    This ordering takes a (preferably total) order on the operators.
    The meaning of the operator ordering is:
    a > b if a should be further in than b.
    That is, things that should float to the outer level should be < the things
    they float over.

    The ordering is as follows.
    - If s_i >= t for any i, then f(s_1, s_2, ... s_m) > t
    - s >= s for all s
    - If f > g and f(s_1, s_2, .. s_m) > t_i for all i
    then f(s_1, s_2, .. s_m) > g(t_1, t_2, ... t_n)
    - If f = g, f(s_1, s_2, ... s_m) > t_j for all j > 2
    and (s_1, s_2, ... s_m) >[lex] (t_1, t_2, ... n_n)
    then f(s_1, s_2, ... s_m) > g(t_1, t_2, ... t_n).

    Here >[lex] on tuples means to go left to right.
    If we see a_i > b_i, then a is >[lex] b.
    If not (a_i >= b_i) while scanning, a is not >[lex] b.
    If b runs out of elements before a while searching, a is >[lex] b"""

    def __init__(self, op_gt: PartialOrder[Operator]) -> None:
        """:param op_gt: Total order (will be transitively closed over)
        on the operators. Send in >"""

        self.op_gt = transitive_closure(op_gt)

    def _lex_gt(self, s_ops: List[Expression],
                t_ops: List[Expression]) -> bool:
        """The lexicographic order on tuples of expressions"""
        for s_i, t_i in zip(s_ops, t_ops):
            if self(s_i, t_i):
                return True
            if not s_i == t_i:
                return False
        return len(s_ops) > len(t_ops)

    def __call__(self, s: Expression, t: Expression) -> bool:
        """Order under the lexicographic path ordering"""
        s_head = to_operator(s)
        t_head = to_operator(t)
        if s_head is None:
            # Whether or not t is an operator, s can't be > to it
            return False

        if t_head is None:
            return True

        if any(self(a, t) or a == t
               for a in operands(s)):  # Empty list is False
            return True

        if (s_head, t_head) in self.op_gt:
            if t_head is None:
                raise(ValueError("Somehow None got into the comparisons"))
            if all(self(s, a) for a in operands(t)):
                return True

        if s_head == t_head:  # Can't be two vars, that's dealt with
            s_ops = operands(s)
            t_ops = operands(t)
            if self._lex_gt(s_ops, t_ops):
                if all(self(s, a) for a in t_ops[1:]):
                    return True

        return False
