#!/usr/bin/env python
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
"""Program entry point"""

from typing import List
from mypy_extensions import NoReturn

import argparse
import sys

from knuth_bendix import metadata
from knuth_bendix.knuth_bendix_ordering import KnuthBendixOrdering
# from knuth_bendix.lex_path_ordering import LexPathOrdering
from knuth_bendix.rewrite_system import RewriteSystem
from matchpy import (Operation, Arity, make_dot_variable, Symbol)


def main(argv: List[str]) -> int:
    """Program entry point.

    :param argv: command-line arguments
    :type argv: :class:`list`
    """
    author_strings = []
    for name, email in zip(metadata.authors, metadata.emails):
        author_strings.append('Author: {0} <{1}>'.format(name, email))

    epilog = '''
{project} {version}

{authors}
URL: <{url}>
'''.format(
        project=metadata.project,
        version=metadata.version,
        authors='\n'.join(author_strings),
        url=metadata.url)

    arg_parser = argparse.ArgumentParser(
        prog=argv[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=metadata.description,
        epilog=epilog)
    arg_parser.add_argument(
        '-V', '--version',
        action='version',
        version='{0} {1}'.format(metadata.project, metadata.version))

    arg_parser.parse_args(args=argv[1:])

    x, y, z = (make_dot_variable(t) for t in ['x', 'y', 'z'])
    times = Operation.new('*', Arity.binary, 'times', infix=True)
    i = Operation.new('i', Arity.unary)
    e = Symbol('e')

    order = KnuthBendixOrdering({times: 0, i: 0, e: 1}, 1,
                                {(i, times), (times, e)})

    equations = [(times(times(x, y), z), times(x, times(y, z))),
                 (times(e, x), x),
                 (times(i(x), x), e)]
    print("Equations:")
    for s, t in equations:
        print(str(s), "=", str(t))

    system = RewriteSystem.from_equations(order, equations)
    system.complete(order)

    print("Completed rules:")
    for r in system.rules:
        print(str(r))
    return 0


def entry_point() -> NoReturn:
    """Zero-argument entry point for use with setuptools/distribute."""
    raise SystemExit(main(sys.argv))


if __name__ == '__main__':
    entry_point()
