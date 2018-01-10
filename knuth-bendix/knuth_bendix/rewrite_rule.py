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
from .utils import substitute

import matchpy

from matchpy import (Expression, get_variables, ManyToOneMatcher,
                     rename_variables)
from typing import (Iterable, Optional, Iterator, Tuple, List,  # noqa: F401
                    Container, Dict)


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
        if not get_variables(right) <= get_variables(left):
            raise(ValueError("Variables on right of rule with no equivalent on the left")) # NOQA
        substitution = ManyToOneMatcher._collect_variable_renaming(left)
        self.left = rename_variables(left, substitution)
        self.right = rename_variables(right, substitution)
        self.lhs = matchpy.Pattern(self.left)

    def apply_match(self, subst: matchpy.Substitution) -> Expression:
        """Apply the given substitution to the right hand side of the rule.

        :param subst: Substitution from a match of the left side of the rule.
        :returns: The right side of the rule with the substitution applied"""
        return substitute(self.right, subst)

    def __repr__(self) -> str:
        """Return a more machine-readable representation of this rule"""
        return "{cls}({left!r}, {right!r})".format(
            cls=self.__class__,
            left=self.left,
            right=self.right)

    def __str__(self) -> str:
        """Return a human-readable depiction of this rule"""
        return "{left!s} -> {right!s}".format(**self.__dict__)


class RewriteRuleList(Iterable[RewriteRule]):
    """A list of :cls:`RewriteRule`s, supporting efficient replacement,
    through matchpy's :cls:`ManyToOneMatcher`"""

    def __init__(self, *rules: RewriteRule) -> None:
        """:param rules: Rewrite rules to add to the object"""
        self.rules = list(rules)
        self._rebuild()

    def _rebuild(self) -> None:
        """Rebuild the :cls:`ManyToOneReplacer` after deletions or changes"""
        self.matcher = ManyToOneMatcher()  # type: ManyToOneMatcher[RewriteRule] # NOQA
        for i in self.rules:
            self.matcher.add(i.lhs, i)

    def append(self, rule: RewriteRule) -> None:
        self.rules.append(rule)
        self.matcher.add(rule.lhs, rule)

    def extend(self, rules: List[RewriteRule]) -> None:
        self.rules.extend(rules)
        for i in rules:
            self.matcher.add(i.lhs, i)

    def replace(self, idx: int, rule: RewriteRule) -> None:
        """Replace :param:`idx` with :param:`rule`"""
        self.rules[idx] = rule
        self._rebuild()

    def delete(self, idx: int) -> None:
        """Delete the :param:`idx`th rule from the list"""
        del self.rules[idx]
        self._rebuild()

    def __iter__(self) -> Iterator[RewriteRule]:
        return iter(self.rules)

    def __len__(self) -> int:
        return len(self.rules)

    def __getitem__(self, idx: int) -> RewriteRule:
        return self.rules[idx]

    def apply_all(self, expr: Expression,
                  max_count: Optional[int] = None) -> Expression:
        """Apply the rules :arg:`expr` until that's impossible

        :param expr: Expression to replace in.
        :param max_count: Maximum number of times to apply a rule, if any
        :returns: Expression with rule applied as much as possible"""
        any_change = True
        apply_count = 0
        while any_change and (max_count is None or apply_count < max_count):
            any_change = False
            for subexpr, pos in expr.preorder_iter():
                try:
                    rule, subst = next(iter(self.matcher.match(subexpr)))
                    new_subexpr = rule.apply_match(subst)
                    new_expr = matchpy.replace(expr, pos, new_subexpr)
                    if not isinstance(new_expr, Expression):
                        raise TypeError("Result of swapping part of an expression by an expression is not an expression")  # NOQA
                    else:
                        expr = new_expr
                    any_change = True
                    apply_count += 1
                    break
                except StopIteration:
                    pass
        return expr

    def apply_each_once(self, expr: Expression,
                        only: Optional[Container[RewriteRule]] = None) ->\
                       Iterable[Tuple[RewriteRule, Expression]]:  # NOQA
        """Apply each rule in the set once to :param:`expr` if possible.

        :param expr: Expression to match against.
        :param only: If present, only record matches from the given rules.
        :returns: A map from rewrite rules to the expressions they produced.
        If a rule matches multiple times, the outermost match is returned."""
        for subexpr, pos in expr.preorder_iter():
            for rule, subst in self.matcher.match(subexpr):
                if only is None or rule in only:
                    new_subexpr = rule.apply_match(subst)
                    new_expr = matchpy.replace(expr, pos, new_subexpr)
                    if not isinstance(new_expr, Expression):
                        raise TypeError("Result of swapping part of an expression by an expression is not an expression")  # NOQA
                    yield (rule, new_expr)
