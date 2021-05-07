Version 1.7
===========

The library has been tested using Agda 2.6.1 and 2.6.1.3.

Highlights
----------

Bug-fixes
---------

* Added missing module `Function.Metric` which re-exports 
  `Function.Metric.(Core/Definitions/Structures/Bundles)`. This module was referred
  to in the documentation of its children but until now was not present.

Non-backwards compatible changes
--------------------------------

* Replaced O(n) implementation of `Data.Nat.Binary.fromℕ` with O(log n). The old
  implementation is maintained under `Data.Nat.Binary.fromℕ'` and proven to be
  equivalent.

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
  pinch : ∀ {n} → Fin n → Fin (suc n) → Fin n
  ```

* Added new proofs to `Data.Fin.Properties`:
  ```agda
  pinch-surjective : ∀ {m} (i : Fin m) → Surjective _≡_ (pinch i)
  pinch-mono-≤ : ∀ {m} (i : Fin m) → (pinch i) Preserves _≤_ ⟶ _≤_
  ```

* Added new proofs to `Data.Nat.Binary.Properties`:
  ```agda
  fromℕ≡fromℕ' : fromℕ ≗ fromℕ'
  toℕ-fromℕ' : toℕ ∘ fromℕ' ≗ id
  fromℕ'-homo-+ : ∀ m n → fromℕ' (m ℕ.+ n) ≡ fromℕ' m + fromℕ' n
  ```

* Rewrote proofs in `Data.Nat.Binary.Properties` for new implementation of `fromℕ`:
  ```agda
  toℕ-fromℕ : toℕ ∘ fromℕ ≗ id
  fromℕ-homo-+ : ∀ m n → fromℕ (m ℕ.+ n) ≡ fromℕ m + fromℕ n
  ```

* Added new proof to `Data.Nat.DivMod`:
  ```agda
  m/n≤m : ∀ m n {≢0} → (m / n) {≢0} ≤ m
  ```
