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
import pytest
from knuth_bendix.knuth_bendix_ordering import KnuthBendixOrdering
from matchpy import (Operation, Arity, make_dot_variable, Symbol)

x, y, z = (make_dot_variable(t) for t in ['x', 'y', 'z'])
times = Operation.new('*', Arity.binary, 'times', infix=True)
i = Operation.new('i', Arity.unary)
e = Symbol('e')
order = KnuthBendixOrdering({times: 0, i: 0, e: 1}, 1,
                            {(i, times), (times, e)})


@pytest.mark.parametrize("left,right", [
    (times(x, e), x),
    (times(e, x), x),
    (times(i(x), x), e),
    (times(x, i(x)), e),
    (times(times(x, y), z), times(x, times(y, z))),
    (i(e), e),
    (times(i(x), times(x, y)), y),
    (times(x, times(i(x), y)), y),
    (i(i(x)), x),
    (i(times(y, x)), times(i(x), i(y))),
])
def test_knuth_bendix_order(left, right):
    assert order(left, right)
