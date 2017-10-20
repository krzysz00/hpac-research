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

from .rewrite_rule import RewriteRule, apply_all, apply_once, apply_all_once
from .unification import (find_overlaps, equal_mod_renaming,
                          proper_contains)

from matchpy import Expression

import copy

from typing import List, Tuple, Callable, TypeVar, Iterable

_T = TypeVar('_T')
GtOrder = Callable[[_T, _T], bool]
"""Ordering such that f(a, b) returns if a > b"""


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
        self.rules = copy.copy(rules)

    def normalize(self, expr: Expression) -> Expression:
        """Rewrite :ref:`expr` as much as possible with the system's rules.

        :param expr: Expression to rewrite. Will be unmodified.
        :returns: A normalized expression"""
        return apply_all(expr, self.rules)

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

    def _canonicalize_system_step(self, order: GtOrder[Expression]) -> bool:
        """Take a step towards making existing rules more well-behaved.
        This normalizes a non-normalized right hand side, if any,
        then steps the rewrite of a left hand side (if possible),
        then deletes rules that are redundant.

        :param order: Ordering on terms to use for certain steps
        of the canonicalization procedure.
        :returns: True if the system was modified, False otherwise"""
        # Normalize RHSs
        for idx, r in enumerate(self.rules):
            new_right = apply_all(r.right, self.rules)
            if not equal_mod_renaming(r.right, new_right):
                self.rules[idx] = RewriteRule(r.left, new_right)
                return True

        # Step normalization of LHSs if possible
        for idx, r in enumerate(self.rules):
            for new_e, other_r in apply_all_once(r.left, self.rules):
                if (proper_contains(other_r.left, r.left)
                    or (equal_mod_renaming(other_r.left, r.left)
                        and order(r.right, other_r.right))):
                    if equal_mod_renaming(new_e, r.right):
                        # We're about to introduce a = a
                        del self.rules[idx]
                        return True
                    else:
                        u, t = self.orient(new_e, r.right, order)
                        self.rules[idx] = RewriteRule(u, t)
                        return True

        # Eliminate redundant rules
        for idx, r in enumerate(self.rules):
            if equal_mod_renaming(r.left, r.right):
                del self.rules[idx]
                return True
        return False

    def complete(self, order: GtOrder[Expression]) -> None:
        """Complete the system by the Knuth-Bendix algorithm.

        """
        iterating = True
        while iterating:
            while self._canonicalize_system_step(order):
                pass
            new_rules = []
            for r1 in self.rules:
                for r2 in self.rules:
                    for expr in find_overlaps(r1.left, r2.left):
                        s = self.normalize(apply_once(expr, r1))
                        t = self.normalize(apply_once(expr, r2))
                        if not equal_mod_renaming(s, t):
                            s_prime, t_prime = self.orient(s, t, order)
                            new_rules.append(RewriteRule(s_prime, t_prime))
            iterating = bool(new_rules)
            self.rules.extend(new_rules)
