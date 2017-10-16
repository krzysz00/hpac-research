# -*- coding: utf-8 -*-
import pytest
from knuth_bendix.rewrite_rule import RewriteRule
from matchpy import Operation, make_dot_variable, Symbol, Arity
from matchpy import replace_all
import matchpy

@pytest.fixture
def inv_pattern():
    """Return the variable 'x', the operation 'inv', of one argument,
    the identity '1', and the rule 'i(x) -> 1 as a dictionary'"""
    inv = Operation.new('inv', Arity.unary)
    ident = Symbol('1')
    x = make_dot_variable('x')
    lhs = inv(x)
    rhs = ident
    return {'rule': RewriteRule(lhs, rhs),
            'ident': ident,
            'x': x,
            'inv': inv}


def test_subst(inv_pattern):
    const = Symbol('a')
    lhs = inv_pattern['inv'](const)
    ret = replace_all(lhs, [inv_pattern['rule']._replacementRule])
    assert ret == inv_pattern['ident']


def test_print(inv_pattern, capsys):
    print(inv_pattern['rule'])
    assert capsys.readouterr() == ("inv(x_) -> 1\n", "")
