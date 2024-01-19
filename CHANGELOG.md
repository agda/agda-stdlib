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

* In `Data.Nat.Divisibility.Core`:
  ```agda
  *-pres-∣  ↦  Data.Nat.Divisibility.*-pres-∣
  ```

New modules
-----------

* Added new files `Data.Fin.Mod` and `Data.Fin.Mod.Properties`

Additions to existing modules
-----------------------------

* In `Data.Fin.Properties`:
  ```agda
  nonZeroIndex : Fin n → ℕ.NonZero n
  ```

* In `Data.List.Relation.Unary.All.Properties`:
  ```agda
  All-catMaybes⁺ : All (Maybe.All P) xs → All P (catMaybes xs)
  Any-catMaybes⁺ : All (Maybe.Any P) xs → All P (catMaybes xs)
  ```

* In `Data.List.Relation.Unary.AllPairs.Properties`:
  ```agda
  catMaybes⁺ : AllPairs (Pointwise R) xs → AllPairs R (catMaybes xs)
  tabulate⁺-< : (i < j → R (f i) (f j)) → AllPairs R (tabulate f)
  ```

* In `Data.Maybe.Relation.Binary.Pointwise`:
  ```agda
  pointwise⊆any : Pointwise R (just x) ⊆ Any (R x)
  ```

* In `Data.Nat.Divisibility`:
  ```agda
  quotient≢0       : m ∣ n → .{{NonZero n}} → NonZero quotient

  m|n⇒n≡quotient*m : m ∣ n → n ≡ quotient * m
  m|n⇒n≡m*quotient : m ∣ n → n ≡ m * quotient
  quotient-∣       : m ∣ n → quotient ∣ n
  quotient>1       : m ∣ n → m < n → 1 < quotient
  quotient-<       : m ∣ n → .{{NonTrivial m}} → .{{NonZero n}} → quotient < n
  n/m≡quotient     : m ∣ n → .{{_ : NonZero m}} → n / m ≡ quotient

  m/n≡0⇒m<n    : .{{_ : NonZero n}} → m / n ≡ 0 → m < n
  m/n≢0⇒n≤m    : .{{_ : NonZero n}} → m / n ≢ 0 → n ≤ m

  nonZeroDivisor : DivMod dividend divisor → NonZero divisor
  ```

* Added new proofs in `Data.Nat.Properties`:
  ```agda
  m≤n+o⇒m∸n≤o : ∀ m n {o} → m ≤ n + o → m ∸ n ≤ o
  m<n+o⇒m∸n<o : ∀ m n {o} → .{{NonZero o}} → m < n + o → m ∸ n < o
  pred-cancel-≤ : pred m ≤ pred n → (m ≡ 1 × n ≡ 0) ⊎ m ≤ n
  pred-cancel-< : pred m < pred n → m < n
  pred-injective : .{{NonZero m}} → .{{NonZero n}} → pred m ≡ pred n → m ≡ n
  pred-cancel-≡ : pred m ≡ pred n → ((m ≡ 0 × n ≡ 1) ⊎ (m ≡ 1 × n ≡ 0)) ⊎ m ≡ n
  ```

* In `Data.Fin.Base`:
  ```agda
  zero⁺ : .⦃ NonZero n ⦄ → Fin n
  ```

* In `Data.Fin.Mod`:
  ```agda
  sucMod  : Fin n → Fin n
  predMod : Fin n → Fin n
  _ℕ+_    : ℕ → Fin n → Fin n
  _+_     : Fin n → Fin m → Fin n
  _-_     : Fin n → Fin m → Fin n
  ```

* In `Data.Fin.Mod.Properties`:
  ```agda
  suc-inject₁           : ∀ i → sucMod (inject₁ i) ≡ F.suc i
  sucMod-fromℕ          : ∀ n → sucMod (fromℕ n) ≡ zero
  suc[fromℕ]≡zero       : ∀ n → sucMod (fromℕ n) ≡ zero
  suc[fromℕ]≡zero⁻¹     : ∀ i : Fin (ℕ.suc n)) → (sucMod i ≡ zero) → i ≡ fromℕ n
  suc[inject₁]≡suc[j]   : ∀ j → sucMod (inject₁ j) ≡ suc j
  suc[inject₁]≡suc[j]⁻¹ : ∀ i j → (sucMod i ≡ suc j) → i ≡ inject₁ j
  suc-injective         : ∀ {i j} → sucMod i ≡ sucMod j → i ≡ j
  ```

* In `Data.Fin.Mod.Induction`:
  ```agda
  induction : ∀ P → P k → (P i → P (sucMod i)) → ∀ i → P i
  ```
