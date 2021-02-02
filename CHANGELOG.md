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
 
Other minor additions
---------------------

* Added new proofs to `Data.Nat.DivMod`:
  ```agda
  m<n⇒m/n≡0     : m < n → (m / n) {n≢0} ≡ 0
  m/n≡1+[m∸n]/n : m ≥ n → (m / n) {n≢0} ≡ 1 + ((m ∸ n) / n) {n≢0}
  /-cancelˡ     : ((m * n) / (m * o)) {mo≢0} ≡ (n / o) {o≢0}
  ```

* Added new proofs to `Data.Nat.Properties`:
  ```agda
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
  ```
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
