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
import matchpy
from matchpy import (Expression, get_variables, get_head, rename_variables,
                     Substitution)
from typing import Optional
from collections import deque


def uniqify_variables(expr: Expression, to_avoid: Expression) -> Expression:
    """Rename the variables in :ref:`expr' so it has no names in common with
    :ref:`to_avoid`

    :param expr: Expression to rename
    :param to_avoid: Expression we want to not collide with
    :returns: :ref:`expr` with the naming collisions fixed"""
    bad_vars = get_variables(expr) & get_variables(to_avoid)
    if not bad_vars:
        return expr
    else:
        names = {n: '_' + n for n in bad_vars}
        return rename_variables(expr, names)


def maybe_add_substitution(sub: Substitution, var: str,
                           replacement: Expression) -> Optional[Substitution]:
    """Add var -> replacement to sub if possible.

    The addition is possible if, for all a -> b in sub,
    b(var -> replacement) does not contain a.

    :param sub: Existing set of substitutions
    :param var: Variable whose substitution is being defined.
    :param replacemnet: Expression that :ref:`var` might be replaced with.
    :returns: New substitutino set including var -> replacement
    or None if this isn't possible"""
    new_substitutions = {var: replacement}
    for v, term in sub.items():
        new_term = matchpy.substitute(term, Substitution({var: replacement}))
        if not isinstance(new_term, Expression):
            return None  # Lists are a problem for us
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
        elif isinstance(t1, matchpy.Wildcard):
            new_subs = maybe_add_substitution(ret, t1.variable_name, t2)
            if new_subs is not None:
                ret = new_subs
            else:
                return None
        elif isinstance(t2, matchpy.Wildcard):
            new_subs = maybe_add_substitution(ret, t2.variable_name, t1)
            if new_subs is not None:
                ret = new_subs
            else:
                return None
        elif (get_head(t1) == get_head(t2) and
              isinstance(t1, matchpy.Operation) and
              isinstance(t2, matchpy.Operation) and
              len(t1.operands) == len(t2.operands)):
            to_operate.extend(zip(t1.operands, t2.operands))
        else:
            return None
    return ret
