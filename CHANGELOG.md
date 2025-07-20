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

Deprecated modules
------------------

Deprecated names
----------------

New modules
-----------

* `Algebra.Properties.BooleanRing`.

* `Algebra.Properties.BooleanSemiring`.

* `Algebra.Properties.CommutativeRing`.

* `Algebra.Properties.Semiring`.

Additions to existing modules
-----------------------------

* In `Algebra.Bundles`:
  ```agda
  record BooleanSemiring _ _ : Set _
  record BooleanRing _ _     : Set _
  ```

* In `Algebra.Consequences.Propositional`:
  ```agda
  binomial-expansion : Associative _∙_ → _◦_ DistributesOver _∙_ →
    ∀ w x y z → ((w ∙ x) ◦ (y ∙ z)) ≡ ((((w ◦ y) ∙ (w ◦ z)) ∙ (x ◦ y)) ∙ (x ◦ z))
  ```

* In `Algebra.Consequences.Setoid`:
  ```agda
  binomial-expansion : Congruent₂ _∙_  → Associative _∙_ → _◦_ DistributesOver _∙_ →
    ∀ w x y z → ((w ∙ x) ◦ (y ∙ z)) ≈ ((((w ◦ y) ∙ (w ◦ z)) ∙ (x ◦ y)) ∙ (x ◦ z))
  ```

* In `Algebra.Lattice.Properties.BooleanAlgebra.XorRing`:
  ```agda
  ⊕-∧-isBooleanRing : IsBooleanRing _⊕_ _∧_ id ⊥ ⊤
  ⊕-∧-booleanRing   : BooleanRing _ _
  ```

* In `Algebra.Structures`:
  ```agda
  record IsBooleanSemiring + * 0# 1# : Set _
  record IsBooleanRing + * - 0# 1# : Set _
  ```
  NB. the latter is based on `IsCommutativeRing`, with the former on `IsSemiring`.

