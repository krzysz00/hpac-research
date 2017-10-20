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
from knuth_bendix.knuth_bendix_ordering import KnuthBendixOrdering
from knuth_bendix.rewrite_system import RewriteSystem
from knuth_bendix.rewrite_rule import RewriteRule
from knuth_bendix.unification import equal_mod_renaming

from matchpy import (Operation, Arity, make_dot_variable, Symbol)

x, y, z = (make_dot_variable(t) for t in ['x', 'y', 'z'])
times = Operation.new('*', Arity.binary, 'times', infix=True)
i = Operation.new('i', Arity.unary)
e = Symbol('e')
order = KnuthBendixOrdering({times: 0, i: 0, e: 1}, 1,
                            {(i, times), (times, e)})


def test_group_theory_completion():
    equations = [(times(times(x, y), z), times(x, times(y, z))),
                 (times(e, x), x),
                 (times(i(x), x), e)]
    expected_system = [
        RewriteRule(times(x, e), x),
        RewriteRule(times(e, x), x),
        RewriteRule(times(i(x), x), e),
        RewriteRule(times(x, i(x)), e),
        RewriteRule(times(times(x, y), z), times(x, times(y, z))),
        RewriteRule(i(e), e),
        RewriteRule(times(i(x), times(x, y)), y),
        RewriteRule(times(x, times(i(x), y)), y),
        RewriteRule(i(i(x)), x),
        RewriteRule(i(times(y, x)), times(i(x), i(y))),
    ]

    system = RewriteSystem.from_equations(order, equations)
    system.complete(order)

    for r in expected_system:
        assert any(equal_mod_renaming(r.left, s.left)
                   and equal_mod_renaming(r.right, s.right)
                   for s in system.rules)
