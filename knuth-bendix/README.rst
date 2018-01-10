=======================
Knuth-Bendix Algorithm
=======================

This is an implementation of the Knuth-Bendix algorithm within `matchpy`.
The main code is in the `rewrite_system` module.

Installation
===========
`pip install -r requirements-dev.txt` to get environment working.

`paver develop` to install for hacking purposes, `paver install` otherwise

`paver test_all` to run every sort of test

The patterns/expressions used by this system cannot contain sequence variables or unnamed wildcards.
Things are liable to break in crazy unforeseen ways if you try it.
