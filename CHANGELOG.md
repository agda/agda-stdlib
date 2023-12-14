Version 2.1-dev
===============

The library has been tested using Agda 2.6.4 and 2.6.4.1.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Other major improvements
------------------------

Deprecated modules
------------------

Deprecated names
----------------

New modules
-----------

* The 'no infinite descent' principle for (accessible elements of) well-founded relations:
  ```
  Induction.NoInfiniteDescent
  ```

Additions to existing modules
-----------------------------

* In `Data.List.Relation.Unary.AllPairs.Properties`:
  ```
  tabulate⁺-< : (i < j → R (f i) (f j)) → AllPairs R (tabulate f)
  ```
  
