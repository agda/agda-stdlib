Version 3.0-dev
===============

The library has been tested using Agda 2.8.0.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

* In `Relation.Nullary.Negation.Core`, all the various types of `contradiction`
  have been weakened as far as possible to make their arguments definitionally
  proof-irrelevant. As a consequence, there is no longer any need for the
  separate v2.4 `contradiction-irr`.

Other major improvements
------------------------

Deprecated modules
------------------

Deprecated names
----------------

New modules
-----------

Additions to existing modules
-----------------------------

* In `Relation.Nullary.Negation.Core`
  ```agda
  ¬¬-η : A → ¬ ¬ A
  ```

* In `Relation.Nullary.Negation.Core`
  ```agda
  ¬¬-η : A → ¬ ¬ A
  ```
