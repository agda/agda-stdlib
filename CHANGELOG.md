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

* In `Data.Nat.Properties`:
  ```agda
  m≤n⇒n⊔m≡n   ↦  m≥n⇒m⊔n≡m
  m≤n⇒n⊓m≡m   ↦  m≥n⇒m⊓n≡n
  n⊔m≡m⇒n≤m   ↦  m⊔n≡n⇒m≤n
  n⊔m≡n⇒m≤n   ↦  m⊔n≡m⇒n≤m
  n≤m⊔n       ↦  m≤n⊔m
  ⊔-least     ↦  ⊔-lub
  ⊓-greatest  ↦  ⊓-glb
  ⊔-pres-≤m   ↦  ⊔-lub
  ⊓-pres-m≤   ↦  ⊓-glb
  ⊔-abs-⊓     ↦  ⊔-absorbs-⊓
  ⊓-abs-⊔     ↦  ⊓-absorbs-⊔
  ```

* In `Data.Integer.Properties`:
  ```agda
  m≤n⇒m⊓n≡m  ↦  i≤j⇒i⊓j≡i
  m⊓n≡m⇒m≤n  ↦  i⊓j≡i⇒i≤j
  m≥n⇒m⊓n≡n  ↦  i≥j⇒i⊓j≡j
  m⊓n≡n⇒m≥n  ↦  i⊓j≡j⇒j≤i
  m⊓n≤n      ↦  i⊓j≤j
  m⊓n≤m      ↦  i⊓j≤i
  m≤n⇒m⊔n≡n  ↦  i≤j⇒i⊔j≡j
  m⊔n≡n⇒m≤n  ↦  i⊔j≡j⇒i≤j
  m≥n⇒m⊔n≡m  ↦  i≥j⇒i⊔j≡i
  m⊔n≡m⇒m≥n  ↦  i⊔j≡i⇒j≤i
  m≤m⊔n      ↦  i≤i⊔j
  n≤m⊔n      ↦  i≤j⊔i
  ```

New modules
-----------

* Specifications for min and max operators
  ```
  Algebra.Construct.NaturalChoice.MinOp
  Algebra.Construct.NaturalChoice.MaxOp
  ```

* Linear congruential pseudo random generators for ℕ.
  /!\ NB: LCGs must not be used for cryptographic applications
  /!\ NB: the example parameters provided are not claimed to be good
  ```
  Data.Nat.PseudoRandom.LCG
  ```

Other minor additions
---------------------

* Added new function in `Data.List.Base`:
  ```agda
  last : List A → Maybe A
  ```

* Added new proofs in `Data.List.Relation.Unary.All.Properties`:
  ```agda
  head⁺ : All P xs → Maybe.All P (head xs)
  tail⁺ : All P xs → Maybe.All (All P) (tail xs)
  last⁺ : All P xs → Maybe.All P (last xs)

  uncons⁺ : All P xs → Maybe.All (P ⟨×⟩ All P) (uncons xs)
  uncons⁻ : Maybe.All (P ⟨×⟩ All P) (uncons xs) → All P xs
  unsnoc⁺ : All P xs → Maybe.All (All P ⟨×⟩ P) (unsnoc xs)
  unsnoc⁻ : Maybe.All (All P ⟨×⟩ P) (unsnoc xs) → All P xs

  dropWhile⁺ : (Q? : Decidable Q) → All P xs → All P (dropWhile Q? xs)
  dropWhile⁻ : (P? : Decidable P) → dropWhile P? xs ≡ [] → All P xs
  takeWhile⁺ : (Q? : Decidable Q) → All P xs → All P (takeWhile Q? xs)
  takeWhile⁻ : (P? : Decidable P) → takeWhile P? xs ≡ xs → All P xs

  all-head-dropWhile : (P? : Decidable P) → ∀ xs → Maybe.All (∁ P) (head (dropWhile P? xs))
  all-takeWhile      : (P? : Decidable P) → ∀ xs → All P (takeWhile P? xs)
  ```

* Added new proofs to `Data.Nat.DivMod`:
  ```agda
  m<n⇒m/n≡0     : m < n → (m / n) {n≢0} ≡ 0
  m/n≡1+[m∸n]/n : m ≥ n → (m / n) {n≢0} ≡ 1 + ((m ∸ n) / n) {n≢0}
  /-cancelˡ     : ((m * n) / (m * o)) {mo≢0} ≡ (n / o) {o≢0}
  ```

* Added new operations to `Data.Fin.Subset`:
  ```
  _─_ : Op₂ (Subset n)
  _-_ : Subset n → Fin n → Subset n
  ```

* Added new proofs to `Data.Fin.Subset.Properties`:
  ```
  s⊂s             : p ⊂ q → s ∷ p ⊂ s ∷ q
  ∣p∣≤∣x∷p∣       : ∣ p ∣ ≤ ∣ x ∷ p ∣

  p─⊥≡p           : p ─ ⊥ ≡ p
  p─⊤≡⊥           : p ─ ⊤ ≡ ⊥
  p─q─r≡p─q∪r     : p ─ q ─ r ≡ p ─ (q ∪ r)
  p─q─r≡p─r─q     : p ─ q ─ r ≡ p ─ r ─ q
  p─q─q≡p─q       : p ─ q ─ q ≡ p ─ q
  p─q⊆p           : p ─ q ⊆ p
  ∣p─q∣≤∣p∣       : ∣ p ─ q ∣ ≤ ∣ p ∣
  p∩q≢∅⇒p─q⊂p     : Nonempty (p ∩ q) → p ─ q ⊂ p
  p∩q≢∅⇒∣p─q∣<∣p∣ : Nonempty (p ∩ q) → ∣ p ─ q ∣ < ∣ p ∣
  x∈p∧x∉q⇒x∈p─q   : x ∈ p → x ∉ q → x ∈ p ─ q

  p─x─y≡p─y─x     : p - x - y ≡ p - y - x
  x∈p⇒p-x⊂p       : x ∈ p → p - x ⊂ p
  x∈p⇒∣p-x∣<∣p|   : x ∈ p → ∣ p - x ∣ < ∣ p ∣
  x∈p∧x≢y⇒x∈p-y   : x ∈ p → x ≢ y → x ∈ p - y
  ```

* Added new proofs to `Data.Nat.Properties`:
  ```agda
  >⇒≢ : _>_ ⇒ _≢_

  pred[n]≤n : pred n ≤ n

  n<1⇒n≡0 : n < 1 → n ≡ 0
  m<n⇒0<n : m < n → 0 < n

  m≤n*m : 0 < n → m ≤ n * m

  ⊔-⊓-absorptive            : Absorptive _⊓_ _

  ⊔-⊓-isLattice             : IsLattice _⊔_ _⊓_
  ⊔-⊓-isDistributiveLattice : IsDistributiveLattice _⊔_ _⊓_

  ⊓-commutativeSemigroup    : CommutativeSemigroup 0ℓ 0ℓ
  ⊔-commutativeSemigroup    : CommutativeSemigroup 0ℓ 0ℓ
  ⊔-0-monoid                : Monoid 0ℓ 0ℓ
  ⊔-⊓-lattice               : Lattice 0ℓ 0ℓ
  ⊔-⊓-distributiveLattice   : DistributiveLattice 0ℓ 0ℓ

  mono-≤-distrib-⊔          : f Preserves _≤_ ⟶ _≤_ → f (x ⊔ y) ≈ f x ⊔ f y
  mono-≤-distrib-⊓          : f Preserves _≤_ ⟶ _≤_ → f (x ⊓ y) ≈ f x ⊓ f y
  antimono-≤-distrib-⊓      : f Preserves _≤_ ⟶ _≥_ → f (x ⊓ y) ≈ f x ⊔ f y
  antimono-≤-distrib-⊔      : f Preserves _≤_ ⟶ _≥_ → f (x ⊔ y) ≈ f x ⊓ f y
  ```

* Added new proofs to `Data.Integer.Properties`:
  ```agda
  ⊓-distribˡ-⊔              : _⊓_ DistributesOverˡ _⊔_
  ⊓-distribʳ-⊔              : _⊓_ DistributesOverʳ _⊔_
  ⊓-distrib-⊔               : _⊓_ DistributesOver  _⊔_
  ⊔-distribˡ-⊓              : _⊔_ DistributesOverˡ _⊓_
  ⊔-distribʳ-⊓              : _⊔_ DistributesOverʳ _⊓_
  ⊔-distrib-⊓               : _⊔_ DistributesOver  _⊓_

  ⊔-⊓-isDistributiveLattice : IsDistributiveLattice _⊔_ _⊓_
  ⊓-⊔-isDistributiveLattice : IsDistributiveLattice _⊓_ _⊔_

  ⊔-⊓-distributiveLattice   : DistributiveLattice _ _
  ⊓-⊔-distributiveLattice   : DistributiveLattice _ _

  ⊓-glb                     : m ≥ o → n ≥ o → m ⊓ n ≥ o
  ⊓-triangulate             : m ⊓ n ⊓ o ≡ (m ⊓ n) ⊓ (n ⊓ o)
  ⊓-mono-≤                  : _⊓_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ⊓-monoˡ-≤                 : (_⊓ n) Preserves _≤_ ⟶ _≤_
  ⊓-monoʳ-≤                 : (n ⊓_) Preserves _≤_ ⟶ _≤_

  ⊔-lub                     : m ≤ o → n ≤ o → m ⊔ n ≤ o
  ⊔-triangulate             : m ⊔ n ⊔ o ≡ (m ⊔ n) ⊔ (n ⊔ o)
  ⊔-mono-≤                  : _⊔_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ⊔-monoˡ-≤                 : (_⊔ n) Preserves _≤_ ⟶ _≤_
  ⊔-monoʳ-≤                 : (n ⊔_) Preserves _≤_ ⟶ _≤_

  i≤j⇒i⊓k≤j                 : i ≤ j → i ⊓ k ≤ j
  i≤j⇒k⊓i≤j                 : i ≤ j → k ⊓ i ≤ j
  i≤j⊓k⇒i≤j                 : i ≤ j ⊓ k → i ≤ j
  i≤j⊓k⇒i≤k                 : i ≤ j ⊓ k → i ≤ k

  i≤j⇒i≤j⊔k                 : i ≤ j → i ≤ j ⊔ k
  i≤j⇒i≤k⊔j                 : i ≤ j → i ≤ k ⊔ j
  i⊔j≤k⇒i≤k                 : i ⊔ j ≤ k → i ≤ k
  i⊔j≤k⇒j≤k                 : i ⊔ j ≤ k → j ≤ k

  i⊓j≤i⊔j                   : i ⊓ j ≤ i ⊔ j
  ```

* Added new proofs to `Relation.Binary.Properties.Poset`:
  ```agda
  mono⇒cong     : f Preserves _≤_ ⟶ _≤_ → f Preserves _≈_ ⟶ _≈_
  antimono⇒cong : f Preserves _≤_ ⟶ _≥_ → f Preserves _≈_ ⟶ _≈_
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

* Added new proof to `Data.List.Relation.Unary.All.Properties`:
  ```agda
  all-upTo : All (_< n) (upTo n)
  ```

* Added new definitions to `IO`:
  ```agda
  getLine : IO String
  Main : Set
  ```
