Version 2.3-dev
===============

The library has been tested using Agda 2.7.0 and 2.7.0.1.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Minor improvements
------------------

Deprecated modules
------------------

Deprecated names
----------------

* In `Data.List.Base`:
  ```agda
  sum       ↦  Data.Nat.ListAction.sum
  product   ↦  Data.Nat.ListAction.product
  ```

* In `Data.List.Properties`:
  ```agda
  sum-++       ↦  Data.Nat.ListAction.sum-++
  ∈⇒∣product   ↦  Data.Nat.ListAction.∈⇒∣product
  product≢0    ↦  Data.Nat.ListAction.product≢0
  ∈⇒≤product   ↦  Data.Nat.ListAction.∈⇒≤product
  ```

* In `Data.List.Relation.Binary.Permutation.Propositional.Properties`:
  ```agda
  sum-↭       ↦  Data.Nat.ListAction.sum-↭
  product-↭   ↦  Data.Nat.ListAction.product-↭
  ```

New modules
-----------

* `Data.List.Base.{sum|product}` and their properties have been lifted out into `Data.Nat.ListAction`.

Additions to existing modules
-----------------------------
