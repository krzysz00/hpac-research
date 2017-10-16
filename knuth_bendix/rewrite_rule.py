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
"""Convenience types for working with rewrite rules.

Matchpy generally has decent types, but they need a bit of specialization
and other elbow grease to make everything behave"""
import matchpy
import math
from matchpy import Expression
from typing import cast, Union, Iterable, Optional


class RewriteRule(object):
    """
    Wrapper around :class:`matchpy.ReplacementRule` to suit our purposes.

    Data here is immutable. Setting the sides won't work all that well.
    """

    def __init__(self, left: Expression, right: Expression) -> None:
        """
        :param left: Expression to find
        :param right: Expression to rewrite to.
        This must have same variables as :arg:`left`
        """
        self.left = left
        self.right = right
        lhs = matchpy.Pattern(left)

        def rhs(**kwargs: Expression) -> Expression:
            return cast(Expression,
                        matchpy.substitute(self.right,
                                           matchpy.Substitution(kwargs)))

        self._replacementRule = matchpy.ReplacementRule(lhs, rhs)

    def __repr__(self) -> str:
        """Return a more machine-readable representation of this rule"""
        return "{cls}({left!r}, {right!r})".format(
            cls=self.__class__,
            left=self.left,
            right=self.right)

    def __str__(self) -> str:
        """Return a human-readable depiction of this rule"""
        return "{left!s} -> {right!s}".format(**self.__dict__)


def _replace_all(expr: Expression,
                 rules: Iterable[matchpy.ReplacementRule],
                 max_count: Union[int, float]=math.inf) -> Expression:
    ret = matchpy.replace_all(expr, rules, max_count=max_count)
    if isinstance(ret, Expression):
        return ret
    else:
        raise(TypeError("Expected rewrite rules to generate expression, got a {}" # NOQA
                        .format(type(ret))))


def apply_once(expr: Expression, rule: RewriteRule) -> Expression:
    """Apply :arg:`rule` to :arg:`rule` once if possible.

    :param expr: Expression to replace in.
    :param rule: Rule to maybe apply to the expression
    :returns: Expression with rule applied once, if possible"""
    return cast(Expression, _replace_all(expr, [rule._replacementRule],
                                         max_count=1))


def apply_all(expr: Expression, rules: Iterable[RewriteRule],
              max_count: Optional[int]=None) -> Expression:
    """Apply :arg:`rules` to :arg:`rule` until that's impossible

    :param expr: Expression to replace in.
    :param rule: Rule to maybe apply to the expression
    :param max_count: Maximum number of times to apply rules, if any
    :returns: Expression with rule applied as much as possible"""
    internal = [rule._replacementRule for rule in rules]
    if max_count is None:
        return cast(Expression, _replace_all(expr, internal))
    else:
        return cast(Expression, _replace_all(expr, internal,
                                             max_count=max_count))
