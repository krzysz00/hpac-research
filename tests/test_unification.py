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
from knuth_bendix.unification import (
    uniqify_variables,
    maybe_add_substitution,
    unify_expressions,
    find_overlaps)
from matchpy import (Operation, Arity, make_dot_variable, Symbol,
                     get_variables, substitute)

plus = Operation.new('+', Arity.polyadic, 'plus', infix=True,
                     associative=True)
f = Operation.new('f', Arity.binary)
g = Operation.new('g', Arity.unary)
h = Operation.new('h', Arity.binary)
x = make_dot_variable('x')
y = make_dot_variable('y')
z = make_dot_variable('z')
a = Symbol('a')
b = Symbol('b')


@pytest.mark.parametrize("left,right,is_changed", [
    (x, x, True),
    (x, y, False),
    (y, x, False),
    (a, x, False),
    (a, b, False),
    (x, a, False),
    (f(x, y), f(x, z), True),
    (f(x, y), f(x, y), True),
    (g(x), g(x), True),
    (g(y), g(z), False),
    (plus(x, y, z), plus(x, y, z, a, b), True),
    (plus(x, y), plus(z, a), False)
])
def test_uniqify_variables(left, right, is_changed):
    left_prime = uniqify_variables(left, right)
    assert not (get_variables(left_prime) & get_variables(right))
    assert (not (left_prime == left)) == is_changed


@pytest.mark.parametrize("subs,var,rule,expected", [
    ({'x': y}, 'y', x, None),
    ({'x': y}, 'y', z, {'x': z, 'y': z}),
    ({'y': g(z)}, 'z', x, {'z': x, 'y': g(x)}),
    ({'y': g(a)}, 'z', x, {'z': x, 'y': g(a)}),
    ({'x': z}, 'x', y, {'x': y}),
    ({'x': f(g(y), z)}, 'z', g(x), None),
    ({'x': f(g(y), z)}, 'y', g(z), {'y': g(z), 'x': f(g(g(z)), z)})
])
def test_maybe_add_substitution(subs, var, rule, expected):
    assert maybe_add_substitution(subs, var, rule) == expected


@pytest.mark.parametrize("left,right,expected", [
    (x, y, {'x': y}),
    (g(x), y, {'y': g(x)}),
    (z, g(a), {'z': g(a)}),
    (g(x), g(a), {'x': a}),
    (f(x, b), f(a, y), {'x': a, 'y': b}),
    (f(x, y), g(x), None),
    (plus(x, y, z), plus(x, y), None),
    (f(f(x, y), z), f(g(x), z), None),
    (f(x, y), f(y, x), None),
])
def test_unify_expressions(left, right, expected):
    assert unify_expressions(left, right) == expected
    sub = unify_expressions(left, right)
    if sub is not None:
        assert substitute(left, sub) == substitute(right, sub)


@pytest.mark.parametrize("term,within,expected", [
    (f(a, x), f(f(x, y), z), [f(f(a, y), z)]),
    (f(g(x), x), f(f(x, y), z), [f(f(g(y), y), z)])
])
def test_find_overlaps(term, within, expected):
    assert find_overlaps(term, within) == expected
