Version 1.7
===========

The library has been tested using Agda 2.6.1 and 2.6.1.3.

Highlights
----------

* List literal syntax for `List`/`Vec`/`Vector`, allowing one to write `[ x , y , z ]`
  instead of `x ∷ y ∷ z ∷ []`.

Bug-fixes
---------

* Added missing module `Function.Metric` which re-exports 
  `Function.Metric.(Core/Definitions/Structures/Bundles)`. This module was referred
  to in the documentation of its children but until now was not present.

Non-backwards compatible changes
--------------------------------

Deprecated modules
------------------

Deprecated names
----------------

New modules
-----------

* Metrics specialised to co-domains with rational numbers:
  ```
  Function.Metric.Rational
  Function.Metric.Rational.Definitions
  Function.Metric.Rational.Structures
  Function.Metric.Rational.Bundles
  ```

* Lists that contain every element of a type:
  ```
  Data.List.Relation.Unary.Complete.Setoid
  Data.List.Relation.Unary.Complete.Setoid.Properties
  ```

Major changes
-------------

* Enhanced the definition of `[_]` in `Data.List` and `Data.Vector` so that one
  can write `[ x , y , z ]` instead of `x ∷ y ∷ z ∷ []`. The implementation is
  uses `Data.Vec.Recursive` which in turn uses `Data.Product` and therefore you
  will need to have `_,_` from `Data.Product` imported for this to work. Note that
  you still cannot use `[_]` in pattern matching.

Other minor additions
---------------------

* Added new relations to `Data.Fin.Base`:
  ```agda
  _≥_ = ℕ._≥_ on toℕ
  _>_ = ℕ._>_ on toℕ
  ```

* Added new proofs to `Data.Fin.Induction`:
  ```agda
  >-wellFounded   : WellFounded {A = Fin n} _>_
  
  <-weakInduction : P zero      → (∀ i → P (inject₁ i) → P (suc i)) → ∀ i → P i
  >-weakInduction : P (fromℕ n) → (∀ i → P (suc i) → P (inject₁ i)) → ∀ i → P i
  ```

* Added new proofs to `Relation.Binary.Properties.Setoid`:
  ```agda
  respʳ-flip : _≈_ Respectsʳ (flip _≈_)
  respˡ-flip : _≈_ Respectsˡ (flip _≈_)
  ```

* Added new function to `Data.Fin.Base`:
  ```agda
  pinch : Fin n → Fin (suc n) → Fin n
  ```

* Added new proofs to `Data.Fin.Properties`:
  ```agda
  pinch-surjective : Surjective _≡_ (pinch i)
  pinch-mono-≤     : (pinch i) Preserves _≤_ ⟶ _≤_
  ```

* Added standard "sugar" for `Data.Vec.Functional`:
  ```agda
  [_] : A ^ (suc n) → Vector A (suc n)
  ```
