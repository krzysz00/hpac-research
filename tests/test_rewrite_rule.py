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
from knuth_bendix.rewrite_rule import (RewriteRule, apply_all, apply_once,
                                       apply_all_once)
from matchpy import Operation, make_dot_variable, Symbol, Arity


@pytest.fixture
def inv_pattern():
    """Return the variable 'x', the operation 'inv', of one argument,
    and the rule 'inv(x) -> x as a dictionary'"""
    inv = Operation.new('inv', Arity.unary)
    x = make_dot_variable('x')
    lhs = inv(x)
    rhs = x
    return {'rule': RewriteRule(lhs, rhs),
            'x': x,
            'inv': inv}


def test_subst(inv_pattern):
    const = Symbol('a')
    lhs = inv_pattern['inv'](const)
    ret = apply_all(lhs, [inv_pattern['rule']])
    assert ret == const


def test_print(inv_pattern, capsys):
    print(inv_pattern['rule'])
    assert capsys.readouterr() == ("inv(x_) -> x_\n", "")


def test_apply_once(inv_pattern):
    const = Symbol('b')
    inv = inv_pattern['inv']
    expr = inv(inv(const))
    ret1 = apply_once(expr, inv_pattern['rule'])
    ret2 = apply_all(expr, [inv_pattern['rule']], max_count=1)
    assert ret1 == ret2
    assert ret1 == inv(const)


def test_apply_all(inv_pattern):
    const = Symbol('b')
    inv = inv_pattern['inv']
    expr = inv(inv(const))
    ret = apply_all(expr, [inv_pattern['rule']])
    assert ret == const


def test_apply_all_many_rules(inv_pattern):
    inv_rule = inv_pattern['rule']
    inv = inv_pattern['inv']
    g = Operation.new('g', Arity.binary)
    y = make_dot_variable('y')
    z = make_dot_variable('z')
    g_rule = RewriteRule(g(y, z), y)

    a = Symbol('a')
    b = Symbol('b')
    c = Symbol('c')
    d = Symbol('d')
    expr = g(inv(g(g(inv(a), b), c)), d)

    ret = apply_all(expr, [inv_rule, g_rule])
    assert ret == a

    assert (list(apply_all_once(expr, [inv_rule, g_rule]))
            == [(g(g(g(inv(a), b), c), d), inv_rule),
                (inv(g(g(inv(a), b), c)), g_rule)])


def test_new_variable_failure():
    x = make_dot_variable('x')
    y = make_dot_variable('y')
    z = make_dot_variable('z')
    f = Operation.new('f', Arity.binary)
    with pytest.raises(ValueError):
        RewriteRule(f(x, y), f(z, x))
