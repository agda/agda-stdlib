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

Additions to existing modules
-----------------------------

* In `Data.Maybe.Relation.Binary.Pointwise`:
  ```agda
  pointwise⊆any : Pointwise R (just x) ⊆ Any (R x)
  ```

* In `Data.List.Relation.Unary.All.Properties`:
  ```agda
  All-catMaybes⁺ : All (Maybe.All P) xs → All P (catMaybes xs)
  Any-catMaybes⁺ : All (Maybe.Any P) xs → All P (catMaybes xs)
  ```

* In `Data.List.Relation.Unary.AllPairs.Properties`:
  ```
  catMaybes⁺ : AllPairs (Pointwise R) xs → AllPairs R (catMaybes xs)
  ```
