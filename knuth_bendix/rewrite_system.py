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
"""An implementation of a rewrite-rule system,
including the Knuth-Bendix completion algorithm"""

from .rewrite_rule import RewriteRule, RewriteRuleList
from .unification import (find_overlaps, equal_mod_renaming,
                          proper_contains)

from matchpy import Expression
from itertools import chain, count
import heapq
from collections import defaultdict

from typing import (List, Tuple, Callable, TypeVar, Iterable,  # noqa: F401
                    Generic, DefaultDict)

_T = TypeVar('_T')

GtOrder = Callable[[_T, _T], bool]
"""Ordering such that f(a, b) returns if a > b"""


class Heap(Generic[_T]):
    """Min-heap wrapper requiring a key function"""
    def __init__(self, key: Callable[[_T], int]) -> None:
        self.key = key
        self.heap = []  # type: List[Tuple[int, int, _T]]
        self.counter = count()

    def push(self, item: _T) -> None:
        """Insert into the heap, computing the priority via key."""
        priority = self.key(item)
        count = next(self.counter)
        heapq.heappush(self.heap, (priority, count, item))

    def popmin(self) -> _T:
        """Pop off the smallest item from the heap"""
        _, _, item = heapq.heappop(self.heap)
        return item

    def __bool__(self) -> bool:
        return bool(self.heap)


def subexpression_count(expr: Expression) -> int:
    """Count the number of nodes in the tree formed by :param:`expr`"""
    return len(list(expr.preorder_iter()))


class CompletionFailure(Exception):
    """Exception indicating that the Knuth-Bendix algorithm
    could not complete on the given rewrite system."""
    pass


class RewriteSystem(object):
    """A class that implements a term-rewriting system.
    Allows for the completion of the system by the Knuth-Bendix algorithm."""

    def __init__(self, rules: List[RewriteRule] = []) -> None:
        """Create a rewrite system with the given initial rules.

        :param rules: A list of rules to initialize the system with.
        Will be shallowly copied"""
        self.rules = RewriteRuleList()
        self.to_extension = {}
        self.from_extension = {}
        for i in rules:
            self.append_rule(i)
        self.critical_pairs = Heap(lambda e: subexpression_count(e[0]) +
                                   subexpression_count(e[1]))  # type: Heap[Tuple[Expression, Expression]]  # NOQA

    def normalize(self, expr: Expression) -> Expression:
        """Rewrite :ref:`expr` as much as possible with the system's rules.

        :param expr: Expression to rewrite. Will be unmodified.
        :returns: A normalized expression"""
        return self.rules.apply_all(expr)

    @staticmethod
    def orient(s: Expression, t: Expression,
               order: GtOrder[Expression]) -> Tuple[Expression, Expression]:
        """Order two expressions according to :ref:`order`.

        :raises: :cls:`CompletionFailure` if orientation isn't possible
        :returns: (s', t') such that s' > t'"""
        s_gt = order(s, t)
        t_gt = order(t, s)
        if not (s_gt ^ t_gt):
            raise(ValueError("{} and {} are not orientable".format(str(s), str(t))))  # NOQA
        elif s_gt:
            return (s, t)
        elif t_gt:
            return (t, s)
        else:
            raise(ValueError("There's only four values for two booleans"))

    @classmethod
    def from_equations(cls,
                       order: GtOrder[Expression],
                       equations: Iterable[Tuple[Expression, Expression]]) ->\
                       'RewriteSystem':  # NOQA
        rules = []
        for s, t in equations:
            left, right = cls.orient(s, t, order)
            rules.append(RewriteRule(left, right))
        return cls(rules)

    def append_rule(self, rule: RewriteRule) -> None:
        """Append this rule to the list of rules,
        preforming extensions if needed."""
        self.rules.append(rule)

    def replace_rule(self, idx: int,
                     new_rule: RewriteRule) -> None:
        """Replace the rule at :param:`idx` with :param:`new_rule`,
        accounting for extensions if needed"""
        self.rules.replace(idx, new_rule)

    def delete_rule(self, idx: int) -> None:
        """Delete a rule and (if needed) its extensions."""
        self.rules.delete(idx)

    def trim_redundant_rules(self) -> bool:
        """Remove rules that are specializations of
        or identical to rules in the set.

        :returns: True if any rules were removed"""
        for idx, r in enumerate(self.rules):
            # This only considers whole-expression matches
            for other_r, subst in self.rules.matcher.match(r.left):
                if other_r == r:
                    continue

                print("Removing redundant rule", str(r))
                self.delete_rule(idx)
                self.trim_redundant_rules()
                return True
        return False

    def _canonicalize_system_step(self, order: GtOrder[Expression]) -> bool:
        """Take a step towards making existing rules more well-behaved.
        This normalizes a non-normalized right hand side, if any,
        then steps the rewrite of a left hand side (if possible),
        then deletes rules that are redundant.

        :param order: Ordering on terms to use for certain steps
        of the canonicalization procedure.
        :returns: True if the system was modified, False otherwise"""
        # Delete specializations and redundancies
        if self.trim_redundant_rules():
            return True

        # Normalize RHSs
        for idx, r in enumerate(self.rules):
            new_right = self.normalize(r.right)
            if not equal_mod_renaming(r.right, new_right):
                new_rule = RewriteRule(r.left, new_right)
                self.replace_rule(idx, new_rule)
                print("Normalized right:", new_rule)
                return True

        # Normalize LHSs as much as possible
        for idx, r in enumerate(self.rules):
            for other_r, new_e in self.rules.apply_each_once(r.left):
                if (proper_contains(other_r.left, r.left)
                    or (equal_mod_renaming(other_r.left, r.left)
                        and order(r.right, other_r.right))):
                    if equal_mod_renaming(new_e, r.right):
                        # We're about to introduce a = a
                        self.delete_rule(idx)
                        print("Left normalizing delete:", r, "gives", new_e)
                        return True
                    else:
                        u, t = self.orient(new_e, r.right, order)
                        new_rule = RewriteRule(u, t)
                        self.replace_rule(idx, new_rule)
                        print("Left normalizing collapse: replace", r,
                              "with", new_rule)
                        return True

        return False

    def _add_critical_pairs_with(self, rule: RewriteRule) -> None:
        for other_rule in self.rules:
            for expr in chain(find_overlaps(rule.left, other_rule.left),
                              find_overlaps(other_rule.left, rule.left)):
                matches = defaultdict(list)  # type: DefaultDict[RewriteRule, List[Expression]] # NOQA
                for r, match in self.rules.apply_each_once(expr,
                                                           [rule, other_rule]):
                    matches[r].append(match)
                for s in matches[rule]:
                    for t in matches[other_rule]:
                        self.critical_pairs.push((s, t))

    def complete(self, order: GtOrder[Expression]) -> None:
        """Complete the system by the Knuth-Bendix algorithm.

        :param order: An ordering to orient rules with
        """
        for i in self.rules:
            self._add_critical_pairs_with(i)

        while self.critical_pairs:
            s, t = self.critical_pairs.popmin()
            s = self.normalize(s)
            t = self.normalize(t)
            if not equal_mod_renaming(s, t):
                s_prime, t_prime = self.orient(s, t, order)
                new_rule = RewriteRule(s_prime, t_prime)
                print("New rule:", str(new_rule))
                self.append_rule(new_rule)
                self._add_critical_pairs_with(new_rule)
                while self._canonicalize_system_step(order):
                    pass
