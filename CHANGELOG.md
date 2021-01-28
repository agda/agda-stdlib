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

* Added new operations to `Data.Fin.Subset`:
  ```
  _─_ : Op₂ (Subset n)
  _-_ : Subset n → Fin n → Subset n
  ```

* Added new proofs to `Data.Fin.Subset.Properties`:
  ```
  s⊂s             : p ⊂ q → s ∷ p ⊂ s ∷ q
  ∣p∣≤∣x∷p∣       : ∣ p ∣ ≤ ∣ x ∷ p ∣
  
  p─q⊆p           : p ─ q ⊆ p
  ∣p─q∣≤∣p∣       : ∣ p ─ q ∣ ≤ ∣ p ∣
  p∩q≢∅⇒p─q⊂p     : Nonempty (p ∩ q) → p ─ q ⊂ p
  p∩q≢∅⇒∣p─q∣<∣p∣ : Nonempty (p ∩ q) → ∣ p ─ q ∣ < ∣ p ∣
  p─q─r≡p─q∪r     : (p ─ q) ─ r ≡ p ─ (q ∪ r)
  p─q─r≡p─r─q     : (p ─ q) ─ r ≡ (p ─ r) ─ q
  x∈p∧x∉q⇒x∈p─q   : x ∈ p → x ∉ q → x ∈ p ─ q
  
  p─x─y≡p─y─x     : (p - x) - y ≡ (p - y) - x
  x∈p⇒p-x⊂p       : x ∈ p → p - x ⊂ p
  x∈p⇒∣p-x∣<∣p|   : x ∈ p → ∣ p - x ∣ < ∣ p ∣
  x∈p∧x≢y⇒x∈p-y   : x ∈ p → x ≢ y → x ∈ p - y
  ```

* Added new proofs in `Data.Rational.Unnormalised.Properties`:
  ```agda
  *-congˡ : LeftCongruent _≃_ _*_
  *-congʳ : RightCongruent _≃_ _*_
  ```

* Added new proofs in `Data.Rational.Properties`:
  ```agda
  toℚᵘ-homo-1/ : ∀ p → toℚᵘ (1/ p) ℚᵘ.≃ ℚᵘ.1/ (toℚᵘ p)
  *-inverseˡ : ∀ p → 1/ p * p ≡ 1ℚ
  *-inverseʳ : ∀ p → p * 1/ p ≡ 1ℚ
  ```
