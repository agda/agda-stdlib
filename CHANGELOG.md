Version 1.6-dev
===============

The library has been tested using Agda 2.6.1 and 2.6.1.1.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Deprecated modules
------------------

Deprecated names
----------------

New modules
-----------

Other minor additions
---------------------

* Added new proofs in `Data.Rational.Unnormalised.Properties`:
  ```agda
  *-congʳ : ∀ p → q ≃ r  → p * q ≃ p * r
  *-congˡ : ∀ p → q ≃ r → q * p ≃ r * p
  ```

* Added new proofs in `Data.Rational.Properties`:
  ```agda
  toℚᵘ-homo-1/ : ∀ p → toℚᵘ (1/ p) ℚᵘ.≃ ℚᵘ.1/ (toℚᵘ p)
  *-inverseˡ : ∀ p → 1/ p * p ≡ 1ℚ
  *-inverseʳ : ∀ p → p * 1/ p ≡ 1ℚ
  ```
