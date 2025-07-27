Version 2.4-dev
===============

The library has been tested using Agda 2.8.0.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Minor improvements
------------------

* The types of `Data.Vec.Base.{truncate|padRight}` have been weakened so
  that the argument of type `m ≤ n` is marked as irrelevant. This should be
  backwards compatible, but does change the equational behaviour of these
  functions to be more eager, because no longer blocking on pattern matching
  on that argument.

Deprecated modules
------------------

Deprecated names
----------------

New modules
-----------

Additions to existing modules
-----------------------------
