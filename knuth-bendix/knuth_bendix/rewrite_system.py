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
from .utils import substitute

import matchpy
from matchpy import Expression, get_head
from itertools import chain, count
import heapq
from collections import defaultdict

from typing import (List, Tuple, Callable, TypeVar, Iterable,  # noqa: F401
                    Generic, DefaultDict, Optional)

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
        """Create a rewrite system from the given equations
        using the given ordering to orient them"""
        rules = []
        for s, t in equations:
            left, right = cls.orient(s, t, order)
            rules.append(RewriteRule(left, right))
        return cls(rules)

    def extend_rule(self, rule: RewriteRule) -> Optional[RewriteRule]:
        """Form the match-extension of the given rule, if one is necessary.

        The operation is as follows:
        If the rule is of the form f(x1, x2 ... xn) -> f(y1, y2, ... ym)
        for f associative and commutative, the extension is
        f(extvar, x1, x2, ... xn) -> f(extvar, y1, y2, ... ym).
        If we have f(x1, x2, .. xn) -> t for t nos starting with f,
        we go to f(extvar, x1, x2, ... xn) -> f(extvar, t).
        Otherwise, there is no extension"""
        if not isinstance(rule.left, matchpy.Operation):
            return None
        if not (rule.left.associative and rule.left.commutative):
            return None
        head_func = get_head(rule.left)
        extend_temp = matchpy.make_dot_variable('__extend_temp')
        new_left = head_func(extend_temp, rule.left)
        new_right = head_func(extend_temp, rule.right)
        new_right = self.normalize(new_right)
        return RewriteRule(new_left, new_right)

    def append_rule(self, rule: RewriteRule) -> None:
        """Append this rule to the list of rules,
        preforming extensions if needed.

        It shall be an invariant that extensions
        come right after their primary in the ruleset."""
        self.rules.append(rule)
        extended = self.extend_rule(rule)
        if extended is not None:
            self.rules.append(extended)
            print("Extending", rule, "->", extended)
            self.to_extension[rule] = extended
            self.from_extension[extended] = rule

    def replace_rule(self, idx: int,
                     new_rule: RewriteRule) -> None:
        """Replace the rule at :param:`idx` with :param:`new_rule`,
        accounting for extensions if needed"""
        old_rule = self.rules[idx]
        self.rules.replace(idx, new_rule)
        if old_rule in self.to_extension:
            old_extension = self.to_extension[old_rule]
            del self.to_extension[old_rule]
            del self.from_extension[old_extension]

            new_extension = self.extend_rule(new_rule)
            if new_extension is not None:
                self.rules.replace(idx + 1, new_extension)
                self.to_extension[new_rule] = new_extension
                self.from_extension[new_extension] = new_rule
            else:
                self.rules.delete(idx + 1)
        if old_rule in self.from_extension:
            raise(NotImplementedError("Haven't implemented this case yet"))

    def delete_rule(self, idx: int) -> None:
        """Delete a rule and (if needed) its extensions."""
        rule = self.rules[idx]
        if rule in self.to_extension:
            self.rules.delete(idx + 1)
            extension = self.to_extension[rule]
            del self.to_extension[rule]
            del self.from_extension[extension]
        if rule in self.from_extension:
            self.rules.delete(idx - 1)
            idx = idx - 1
            short = self.from_extension[rule]
            del self.from_extension[rule]
            del self.to_extension[short]
        self.rules.delete(idx)

    def remove_extension(self, idx) -> None:
        """De-extend a rule, given the index of the extension"""
        ext = self.rules[idx]
        raw = self.from_extension[ext]
        del self.from_extension[ext]
        del self.to_extension[raw]
        self.delete_rule(idx)

    def trim_redundant_rules(self) -> bool:
        """Remove rules that are specializations of
        or identical to rules in the set.

        :returns: True if any rules were removed"""
        for idx, r in enumerate(self.rules):
            # This only considers whole-expression matches
            for other_r, subst in self.rules.matcher.match(r.left):
                if other_r == r:
                    continue

                if self.to_extension.get(r, None) == other_r:
                    continue

                if (r in self.from_extension
                     and self.from_extension[r] == other_r):  # noqa: E127
                    print("Removing redundant self-extension", str(r))
                    self.remove_extension(idx)
                    self.trim_redundant_rules()
                    return True

                if (substitute(r.right, subst)
                     != substitute(other_r.right, subst)):  # noqa: E127
                    continue

                if r in self.from_extension:
                    print("Removing redundant extension", str(r))
                    self.remove_extension(idx)
                    self.trim_redundant_rules()
                    return True
                else:
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
            if r in self.from_extension:
                continue
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

            match_rules = [rule, other_rule]
            representative = {rule: rule, other_rule: other_rule}
            if rule in self.to_extension:
                representative[self.to_extension[rule]] = rule
                match_rules.append(self.to_extension[rule])
            if other_rule in self.to_extension:
                representative[self.to_extension[other_rule]] = other_rule
                match_rules.append(self.to_extension[other_rule])
            if rule in self.from_extension:
                representative[self.from_extension[rule]] = rule
                match_rules.append(self.from_extension[rule])
            if other_rule in self.from_extension:
                representative[self.from_extension[other_rule]] = other_rule
                match_rules.append(self.from_extension[other_rule])

            for expr in chain(find_overlaps(rule.left, other_rule.left),
                              find_overlaps(other_rule.left, rule.left)):
                matches = defaultdict(list)  # type: DefaultDict[RewriteRule, List[Expression]] # NOQA

                for r, match in self.rules.apply_each_once(expr, match_rules):
                    matches[representative[r]].append(match)
                for s in matches[rule]:
                    for t in matches[other_rule]:
                        self.critical_pairs.push((s, t))

    def complete(self, order: GtOrder[Expression]) -> None:
        """Complete the system by the Knuth-Bendix algorithm.

        :param order: An ordering to orient rules with
        """
        for i in self.rules:
            self._add_critical_pairs_with(i)

        while self._canonicalize_system_step(order):
            pass

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
                if new_rule in self.to_extension:
                    self._add_critical_pairs_with(self.to_extension[new_rule])
                while self._canonicalize_system_step(order):
                    pass
