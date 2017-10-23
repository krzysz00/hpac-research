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
"""Unification of two terms and associated functionality"""
from .utils import substitute

import matchpy
from matchpy import (Expression, get_variables, get_head, rename_variables,
                     Substitution, Wildcard)
from typing import Optional, Iterator, Tuple, Deque, Dict  # noqa: F401
from collections import deque


def unique_variables_map(expr: Expression,
                         to_avoid: Expression) -> Dict[str, str]:
    """Show what should be renamed in :ref:`expr'
    so it has no names in common with :ref:`to_avoid`

    :param expr: Expression to rename
    :param to_avoid: Expression we want to not collide with
    :returns: Dictionary of variable substitutons"""
    ret = {}  # type: Dict[str, str]
    bad_vars = get_variables(expr) & get_variables(to_avoid)
    for name in bad_vars:
        ret[name] = '_' + name
        while ret[name] in bad_vars:
            ret[name] = '_' + ret[name]
    return ret


def uniqify_variables(expr: Expression, to_avoid: Expression) -> Expression:
    """Rename the variables in :ref:`expr' so it has no names in common with
    :ref:`to_avoid`

    :param expr: Expression to rename
    :param to_avoid: Expression we want to not collide with
    :returns: :ref:`expr` with the naming collisions fixed"""
    names = unique_variables_map(expr, to_avoid)
    return rename_variables(expr, names)


def maybe_add_substitution(sub: Substitution, var: str,
                           replacement: Expression,) -> Optional[Substitution]:
    """Add var -> replacement to sub if possible.

    The addition is possible if, for all a -> b in sub,
    b(var -> replacement) does not contain a.

    :param sub: Existing set of substitutions
    :param var: Variable whose substitution is being defined.
    :param replacemnet: Expression that :ref:`var` might be replaced with.
    :returns: New substitutino set including var -> replacement
    or None if this isn't possible"""
    new_substitutions = {var: replacement}
    if matchpy.contains_variables_from_set(replacement, {var}):
        return None  # Occurs check failed
    for v, term in sub.items():
        new_term = substitute(term, Substitution({var: replacement}))
        if matchpy.contains_variables_from_set(new_term, {v}):
            return None  # Occurs check failed
        if new_term != term:
            new_substitutions[v] = new_term
    return Substitution(sub, **new_substitutions)


def unify_expressions(left: Expression,
                      right: Expression) -> Optional[Substitution]:
    """Return a substitution alpha such that
    :ref:`left` * alpha == :ref:`right` * alpha,
    or None if none such exists.

    For best results, the expressions should not share variables.
    This function does not ensure that

    :param left: An expression to unify.
    :param right: An expression to unify
    :returns: The unifying substitution, or None"""
    ret = Substitution()
    to_operate = deque([(left, right)])
    while to_operate:
        t1, t2 = to_operate.popleft()
        if t1 == t2:
            continue
        any_change = False
        if isinstance(t1, Wildcard):
            new_subs = maybe_add_substitution(ret, t1.variable_name, t2)
            if new_subs is not None:
                ret = new_subs
                any_change = True
            else:
                return None
        elif isinstance(t2, Wildcard):
            new_subs = maybe_add_substitution(ret, t2.variable_name, t1)
            if new_subs is not None:
                ret = new_subs
                any_change = True
            else:
                return None
        elif (get_head(t1) == get_head(t2)
              and isinstance(t1, matchpy.Operation)
              and isinstance(t2, matchpy.Operation)
              and len(t1.operands) == len(t2.operands)):
            # Unify within functions
            to_operate.extendleft(reversed(list(zip(t1.operands,
                                                    t2.operands))))
        else:
            return None

        if any_change:
            new_queue = deque()  # type: Deque[Tuple[Expression, Expression]]
            while to_operate:
                a, b = to_operate.popleft()
                new_a = substitute(a, ret)
                new_b = substitute(b, ret)
                new_queue.append((new_a, new_b))
            to_operate = new_queue
    return ret


def find_overlaps(term: Expression, within: Expression) ->\
                  Iterator[Expression]:
    """Find all overlaps between :ref:`term` and a subterm of :ref:`within'.

    :param term: Expression to look forbid
    :param within: Expression to try and put :ref:`term` in to
    :returns: For every overlap, :ref:`within` unified with :ref:`term`,
    using the substitution for the relevant subterms"""
    term = uniqify_variables(term, within)
    for subterm, _ in within.preorder_iter():
        if not isinstance(subterm, Wildcard):
            sigma = unify_expressions(term, subterm)
            if sigma is not None:
                # Don't bother with trivial substitutions
                # if not all(isinstance(t, Wildcard)
                #           or equal_mod_renaming(t, term)
                #           or equal_mod_renaming(t, subterm)
                #            or equal_mod_renaming(t, within)
                #           for t in sigma.values()):
                overlapped_term = substitute(within, sigma)
                assert equal_mod_renaming(substitute(term, sigma),
                                          substitute(subterm, sigma))
                yield overlapped_term


def equal_mod_renaming(t1: Expression, t2: Expression) -> bool:
    """Determines if :ref:`t1` and :ref:`t2 are equal up to variable renaming.

    :returns: Indication of the two expressions are syntactically equal"""
    if len(get_variables(t1)) != len(get_variables(t2)):
        return False
    sub = unify_expressions(t1, t2)
    return sub is not None and all((isinstance(t, Wildcard)
                                    for t in sub.values()))


def proper_contains(term: Expression,
                    within: Expression) -> bool:
    """Determines if :ref:`term` is a proper subterm of :ref:`within`
    but :ref:`term` != :ref:`within`, up to renaming of variables.

    :param term: Term to find
    :param within: Term to look in
    :returns: Whether term < within under containment"""
    for subterm, position in within.preorder_iter():
        if position:  # Root is ()
            if equal_mod_renaming(term, subterm):
                return True
    return False
