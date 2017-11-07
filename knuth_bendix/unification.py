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
                     Substitution, Wildcard, Operation)

from typing import (Optional, Iterator, Tuple, Deque, Dict, List,  # noqa: F401
                    NamedTuple, TypeVar, Iterable, Sequence, DefaultDict, Any)

from copy import copy
from collections import deque, defaultdict
from multiset import Multiset
import itertools
import numpy as np  # type: ignore


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
        ret[name] = name + "_u"
        while ret[name] in bad_vars:
            ret[name] = ret[name] + "_u"
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


def to_bitfield(x: int, n_bits: int) -> List[bool]:
    """Treating :param:`x` as an :param:`n_bits` long number,
    give a list of the bits in :param:`x`, represented as booleans.

    Most significant bit of :param:`x` appears first on the list"""
    return [bool((x >> i) & 1) for i in range(n_bits - 1, -1, -1)]


def from_bitfield(lst: Iterable[bool]) -> int:
    """Convert an iterable of booleans to a binary number."""
    ret = 0
    for i in lst:
        ret = ret << 1
        if i:
            ret += 1
    return ret


def all_boolean_matrices(m, n):
    # type: (int, int) -> Iterator[np.ndarray[bool]]
    """Return all m x n boolean matrices"""
    yield from (np.reshape(np.array(list(map(lambda r: to_bitfield(r, n),
                                             rows)),
                                    dtype=bool),
                           (m, n))  # Avoid a crash on 0-length arrays
                for rows in itertools.product(range(0, 2 ** n), repeat=m))


class AcOperands(NamedTuple):
    """Convenience for sorting out the operands to AC functions.

    We'll need this foralgorithm reasons"""
    consts: List[Expression]  # noqa: E999, E701
    terms: List[Expression]  # noqa: E701
    vars: List[Expression]  # noqa: E701


def to_ac_operands(ops):
    # type: (Multiset[Expression]) -> AcOperands
    """Sort all the (deduplicated) operands of an AC function by type.

    Because of how multiset iteration works,
    this'll keep identical things next to each other"""
    ret = AcOperands([], [], [])
    for i in ops:
        if isinstance(i, matchpy.Symbol):
            ret.consts.append(i)
        elif isinstance(i, Wildcard):
            ret.vars.append(i)
        else:
            ret.terms.append(i)
    return ret


def some_pairs_sorted(lst: Sequence[int],
                      idxs: Sequence[int]) -> bool:
    """Determine if there is an i in :param:`idxs` such that
    `lst[i]` <= `lst[i + 1]`.

    For the AC unification algorithm, this implies we have a violation of
    the ordering constraint."""
    return any(lst[i] < lst[i + 1] for i in idxs)


def ints_walking_range(min: int, max: int,
                       n: int) -> Iterator[Tuple[int, ...]]:
    """All the n-tuples of integers with elements in [min, max)"""
    yield from itertools.product(
        range(min, max),
        repeat=n)


_T = TypeVar('_T')
def safe_index(lst: List[_T], item: _T) -> Optional[int]:  # noqa: E302
    """Index of a given `item` in `lst`, or `None` if it's not found"""
    try:
        return lst.index(item)
    except ValueError:
        return None


def compare_equal_variable_vectors(idx,
                                   my_vec, their_vec,
                                   idxs_from_constants,
                                   idxs_from_terms):
    # type: (int, np.ndarray[bool], np.ndarray[bool], Sequence[int], Sequence[int]) -> bool # noqa: E501
    """my and theirs are slices from the variable matrix we want to compare.
    The idxs have values that are indices of things that run in the direction
    of my and theirs.

    Returns True if my < theirs as a binary number, False otherwise"""
    var_start = len(idxs_from_constants) + len(idxs_from_terms)
    term_start = len(idxs_from_constants)

    my_vec = np.pad(my_vec, (var_start, 0),
                    'constant', constant_values=False)
    their_vec = np.pad(their_vec, (var_start, 0),
                       'constant', constant_values=False)
    search = idx + var_start
    for field, val in enumerate(idxs_from_constants):
        if val == search:
            my_vec[field] = True
        if val == search + 1:
            their_vec[field] = True
    for field, val in enumerate(idxs_from_terms):
        if val == search:
            my_vec[field + term_start] = True
        if val == search + 1:
            their_vec[field + term_start] = True
        if from_bitfield(my_vec) >= from_bitfield(their_vec):
            return False
    return True


def ac_operand_lists(t1: Operation, t2: Operation)\
                    -> List[List[Tuple[Expression, Expression]]]:
    """Find all the sets of operand unification problems
    we can get from t1 and t2"""
    # Remove common operations
    t1_op_set = Multiset(t1.operands)
    t2_op_set = Multiset(t2.operands)
    common_ops = t1_op_set & t2_op_set
    t1_op_set -= common_ops
    t2_op_set -= common_ops

    t1_duplicate_vars = any(isinstance(e, Wildcard) and n > 1
                            for e, n in t1_op_set.items())
    t2_duplicate_vars = any(isinstance(e, Wildcard) and n > 1
                            for e, n in t2_op_set.items())
    if t1_duplicate_vars and t2_duplicate_vars:
        raise(NotImplementedError("Possible nontermination on this algo, dispatch slowward"))  # noqa
    elif t1_duplicate_vars or t2_duplicate_vars:
        print("Redundant solutions really gosh darn likely")

    ret = []

    op_function = get_head(t1)

    t1_ops = to_ac_operands(t1_op_set)
    t2_ops = to_ac_operands(t2_op_set)

    all_t1_ops = t1_ops.consts + t1_ops.terms + t1_ops.vars
    all_t2_ops = t2_ops.consts + t2_ops.terms + t2_ops.vars

    t1_n_consts = len(t1_ops.consts)
    t2_n_consts = len(t2_ops.consts)
    t1_n_terms = len(t1_ops.terms)
    t2_n_terms = len(t2_ops.terms)
    t1_n_vars = len(t1_ops.vars)
    t2_n_vars = len(t2_ops.vars)
    t1_n_ops = len(all_t1_ops)
    t2_n_ops = len(all_t2_ops)

    t1_var_start = t1_n_ops - t1_n_vars
    t2_var_start = t2_n_ops - t2_n_vars

    t1_equal_consts = [idx for idx in range(0, t1_n_consts - 1)
                       if t1_ops.consts[idx] == t1_ops.consts[idx + 1]]
    t2_equal_consts = [idx for idx in range(0, t2_n_consts - 1)
                       if t2_ops.consts[idx] == t2_ops.consts[idx + 1]]
    t1_equal_terms = [idx for idx in range(0, t1_n_terms - 1)
                      if t1_ops.terms[idx] == t1_ops.terms[idx + 1]]
    t2_equal_terms = [idx for idx in range(0, t2_n_terms - 1)
                      if t2_ops.terms[idx] == t2_ops.terms[idx + 1]]
    t1_equal_vars = [idx for idx in range(0, t1_n_vars - 1)
                     if t1_ops.vars[idx] == t1_ops.vars[idx + 1]]
    t2_equal_vars = [idx for idx in range(0, t2_n_vars - 1)
                     if t2_ops.vars[idx] == t2_ops.vars[idx + 1]]

    for const_rows_true_idx in ints_walking_range(t2_var_start,
                                                  t2_n_ops,
                                                  t1_n_consts):
        # Drop clear violations of the repeat property here
        if some_pairs_sorted(const_rows_true_idx, t1_equal_consts):
            continue

        for const_cols_true_idx in ints_walking_range(t1_var_start,
                                                      t1_n_ops,
                                                      t2_n_consts):
            if some_pairs_sorted(const_cols_true_idx, t2_equal_consts):
                continue

            for term_rows_true_idx in ints_walking_range(t2_n_consts,
                                                         t2_n_ops,
                                                         t1_n_terms):
                if some_pairs_sorted(term_rows_true_idx, t1_equal_terms):
                    continue

                for term_cols_true_idx in ints_walking_range(t1_n_consts,
                                                             t1_n_ops,
                                                             t2_n_terms):
                    if some_pairs_sorted(term_cols_true_idx, t2_equal_terms):
                        continue

                    # Term mismatch
                    if any(row_nr < t1_var_start
                           and (term_rows_true_idx[row_nr - t1_n_consts]
                                != rel_col_nr + t2_n_consts)
                           for rel_col_nr, row_nr
                           in enumerate(term_cols_true_idx)):
                        continue

                    if any(col_nr < t2_var_start
                           and (term_cols_true_idx[col_nr - t2_n_consts]
                                != rel_row_nr + t1_n_consts)
                           for rel_row_nr, col_nr
                           in enumerate(term_rows_true_idx)):
                        continue

                    set_cols = (set(const_rows_true_idx)
                                | set(term_rows_true_idx))
                    set_rows = (set(const_cols_true_idx)
                                | set(term_cols_true_idx))

                    for var_mat in all_boolean_matrices(t1_n_vars, t2_n_vars):
                        # Filter out failures of unification
                        if any(row_sum == 0
                               and raw_idx[0] + t1_var_start not in set_rows
                               for raw_idx, row_sum
                               in np.ndenumerate(np.sum(var_mat, axis=1))):
                            continue

                        if any(col_sum == 0
                               and raw_idx[0] + t2_var_start not in set_cols
                               for raw_idx, col_sum
                               in np.ndenumerate(np.sum(var_mat, axis=0))):
                            continue

                        if any(compare_equal_variable_vectors(
                                i, var_mat[i, :], var_mat[i + 1, :],
                                const_cols_true_idx, term_cols_true_idx)
                               for i in t1_equal_vars):
                            continue
                        if any(compare_equal_variable_vectors(
                                i, var_mat[:, i], var_mat[:, i + 1],
                                const_rows_true_idx, term_rows_true_idx)
                               for i in t2_equal_vars):
                            continue

                        operand_tuples = []
                        t1_var_unifiers = defaultdict(list)  # type: DefaultDict[Expression, List[Expression]] # noqa: E501
                        t2_var_unifiers = defaultdict(list)  # type: DefaultDict[Expression, List[Expression]] # noqa: E501
                        for const, var_idx in zip(t1_ops.consts,
                                                  const_rows_true_idx):
                            var = all_t2_ops[var_idx]
                            t2_var_unifiers[var].append(const)
                        for const, var_idx in zip(t2_ops.consts,
                                                  const_cols_true_idx):
                            var = all_t1_ops[var_idx]
                            t1_var_unifiers[var].append(const)
                        for term, var_idx in zip(t1_ops.terms,
                                                 term_rows_true_idx):
                            expr = all_t2_ops[var_idx]
                            if isinstance(expr, Wildcard):
                                t2_var_unifiers[expr].append(term)
                            else:
                                operand_tuples.append((term, expr))
                        for term, var_idx in zip(t2_ops.terms,
                                                 term_cols_true_idx):
                            expr = all_t1_ops[var_idx]
                            if isinstance(expr, Wildcard):
                                t1_var_unifiers[expr].append(term)
                            # Else case handled above

                        for idxs in np.transpose(np.nonzero(var_mat)):
                            print(idxs)
                            row = t1_ops.vars[idxs[0]]
                            col = t2_ops.vars[idxs[1]]
                            t1_var_unifiers[row].append(col)
                            t2_var_unifiers[col].append(row)
                        for d in [t1_var_unifiers, t2_var_unifiers]:
                            for var, ops in d.items():
                                if len(ops) == 1:
                                    operand_tuples.append((var, ops[0]))
                                else:
                                    operand_tuples.append((var,
                                                           op_function(*ops)))

                        ret.append(operand_tuples)
    return ret


def unify_expressions(left: Expression,
                      right: Expression) -> List[Substitution]:
    """Return a substitution alpha such that
    :ref:`left` * alpha == :ref:`right` * alpha,
    or None if none such exists.

    For best results, the expressions should not share variables.
    This function does not ensure that

    :param left: An expression to unify.
    :param right: An expression to unify
    :returns: The unifying substitution, or None"""
    main_ret = []

    root_ret = Substitution()
    root_to_operate = deque([(left, right)])
    operations = [(root_ret, root_to_operate)]
    while operations:
        preserve_this = True
        ret, to_operate = operations.pop()

        if not to_operate:  # Successful unification
            main_ret.append(ret)
            continue

        t1, t2 = to_operate.popleft()
        if t1 == t2:
            operations.append((ret, to_operate))
            continue

        any_change = False
        if isinstance(t1, Wildcard):
            new_subs = maybe_add_substitution(ret, t1.variable_name, t2)
            if new_subs is not None:
                ret = new_subs
                any_change = True
            else:
                continue  # Here we drop the branch
        elif isinstance(t2, Wildcard):
            new_subs = maybe_add_substitution(ret, t2.variable_name, t1)
            if new_subs is not None:
                ret = new_subs
                any_change = True
            else:
                continue
        elif (get_head(t1) == get_head(t2)
              and isinstance(t1, Operation)
              and isinstance(t2, Operation)):
            # Unify within functions
            if t1.associative and t1.commutative:
                potential_unifiers = ac_operand_lists(t1, t2)
                preserve_this = False
                for i in potential_unifiers:
                    new_ret = copy(ret)
                    new_to_operate = copy(to_operate)
                    new_to_operate.extend(i)
                    operations.append((new_ret, new_to_operate))
            elif t1.associative or t1.commutative:
                raise(NotImplementedError("Straight associative or commutative ain't happening"))  # noqa
            elif len(t1.operands) == len(t2.operands):
                to_operate.extend((zip(t1.operands, t2.operands)))
            else:
                continue
        else:
            continue

        if any_change:
            new_queue = deque()  # type: Deque[Tuple[Expression, Expression]]
            while to_operate:
                a, b = to_operate.popleft()
                new_a = substitute(a, ret)
                new_b = substitute(b, ret)
                new_queue.append((new_a, new_b))
            to_operate = new_queue

        if preserve_this:
            operations.append((ret, to_operate))

    return main_ret


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
            sigmas = unify_expressions(term, subterm)
            for sigma in sigmas:
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
    t1_sub = matchpy.ManyToOneMatcher._collect_variable_renaming(t1)
    t2_sub = matchpy.ManyToOneMatcher._collect_variable_renaming(t2)

    t1_canonical = matchpy.rename_variables(t1, t1_sub)
    t2_canonical = matchpy.rename_variables(t2, t2_sub)
    return t1_canonical == t2_canonical


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
