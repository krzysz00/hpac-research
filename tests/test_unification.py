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
    find_overlaps,
    equal_mod_renaming,
    proper_contains)
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
    (x, y, [{'x': y}]),
    (g(x), y, [{'y': g(x)}]),
    (z, g(a), [{'z': g(a)}]),
    (g(x), g(a), [{'x': a}]),
    (f(x, b), f(a, y), [{'x': a, 'y': b}]),
    (f(x, y), g(x), []),
    (plus(x, y, z), plus(x, y), []),
    (f(f(x, y), z), f(g(x), z), []),
    (f(x, y), f(y, x), [{'x': y}]),
    (f(g(x), x), f(g(a), y), [{'x': a, 'y': a}]),
])
def test_unify_expressions(left, right, expected):
    assert unify_expressions(left, right) == expected
    subs = unify_expressions(left, right)
    for sub in subs:
        assert substitute(left, sub) == substitute(right, sub)


@pytest.mark.parametrize("term,within,expected", [
    (f(a, x), f(f(x, y), z), [f(f(a, y), z)]),
    (f(g(x), x), f(f(x, y), z), [f(f(g(y), y), z)]),
    (g(g(x)), f(y, z), []),
    (g(x), g(y), [g(y)])
])
def test_find_overlaps(term, within, expected):
    assert list(find_overlaps(term, within)) == expected


@pytest.mark.parametrize("t1,t2,expected", [
    (x, x, True),
    (x, y, True),
    (g(x), g(y), True),
    (g(x), g(x), True),
    (f(x, y), f(y, z), True),
    (a, b, False),
    (f(x, y), f(z, a), False),
    (f(x, x), f(y, z), False),
    (f(x, y), g(z), False),
    (f(f(x, y), z), f(x, f(y, z)), False),
    (g(a), g(b), False),
])
def test_equal_mod_renaming(t1, t2, expected):
    assert equal_mod_renaming(t1, t2) == expected


@pytest.mark.parametrize("term,within,expected", [
    (x, x, False),
    (x, y, False),
    (x, g(x), True),
    (x, g(y), True),
    (f(x, y), f(y, z), False),
    (f(x, y), g(f(y, z)), True),
    (a, b, False),
    (a, g(a), True),
    (f(a, b), f(f(a, b), y), True),
])
def test_proper_contains(term, within, expected):
    assert proper_contains(term, within) == expected
