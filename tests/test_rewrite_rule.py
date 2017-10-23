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
from knuth_bendix.rewrite_rule import (RewriteRule, RewriteRuleList)
from matchpy import Operation, make_dot_variable, Symbol, Arity


@pytest.fixture
def inv_pattern():
    """Return the variable 'x', the operation 'inv', of one argument,
    and the rule 'inv(x) -> x as a dictionary'"""
    inv = Operation.new('inv', Arity.unary)
    x = make_dot_variable('x')
    lhs = inv(x)
    rhs = x
    rule = RewriteRule(lhs, rhs)
    rules = RewriteRuleList(rule)
    return {'rule': rule,
            'x': x,
            'inv': inv,
            'rules': rules}


def test_subst(inv_pattern):
    const = Symbol('a')
    lhs = inv_pattern['inv'](const)
    ret = inv_pattern['rules'].apply_all(lhs)
    assert ret == const


def test_print(inv_pattern, capsys):
    print(inv_pattern['rule'])
    assert capsys.readouterr() == ("inv(x_) -> x_\n", "")


def test_apply_once(inv_pattern):
    const = Symbol('b')
    inv = inv_pattern['inv']
    expr = inv(inv(const))
    rules = inv_pattern['rules']
    match_r, ret1 = next(rules.apply_each_once(expr))
    assert match_r == inv_pattern['rule']
    ret2 = rules.apply_all(expr, max_count=1)
    assert ret1 == ret2
    assert ret1 == inv(const)


def test_apply_all(inv_pattern):
    const = Symbol('b')
    inv = inv_pattern['inv']
    expr = inv(inv(const))
    ret = inv_pattern['rules'].apply_all(expr)
    assert ret == const


def test_apply_all_many_rules(inv_pattern):
    rules = inv_pattern['rules']
    inv = inv_pattern['inv']
    inv_rule = inv_pattern['rule']

    g = Operation.new('g', Arity.binary)
    y = make_dot_variable('y')
    z = make_dot_variable('z')
    g_rule = RewriteRule(g(y, z), y)

    rules.append(g_rule)

    a = Symbol('a')
    b = Symbol('b')
    c = Symbol('c')
    d = Symbol('d')
    expr = g(inv(g(g(inv(a), b), c)), d)

    ret = rules.apply_all(expr)
    assert ret == a

    assert (set(rules.apply_each_once(expr, only=[inv_rule, g_rule]))
            == {(inv_rule, g(g(g(inv(a), b), c), d)),
                (inv_rule, g(inv(g(g(a, b), c)), d)),
                (g_rule, inv(g(g(inv(a), b), c))),
                (g_rule, g(inv(g(inv(a), b)), d)),
                (g_rule, g(inv(g(inv(a), c)), d))})


def test_new_variable_failure():
    x = make_dot_variable('x')
    y = make_dot_variable('y')
    z = make_dot_variable('z')
    f = Operation.new('f', Arity.binary)
    with pytest.raises(ValueError):
        RewriteRule(f(x, y), f(z, x))
