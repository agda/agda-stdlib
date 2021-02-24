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
  ∣m+n-m+o∣≡∣n-o| ↦ ∣m+n-m+o∣≡∣n-o∣ -- note final character is a \| rather than a |
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

* In `Data.Rational.Properties`:
  ```agda
  neg-mono-<-> ↦ neg-mono-<
  neg-mono-≤-≥ ↦ neg-mono-≤
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

* Added new operations to `Data.Fin.Base`:
  ```agda
  remQuot : remQuot : ∀ k → Fin (n * k) → Fin n × Fin k
  combine : Fin n → Fin k → Fin (n * k)
  ```

* Added new proofs to `Data.Fin.Properties`:
  ```agda
  remQuot-combine : ∀ x y → remQuot k (combine x y) ≡ (x , y)
  combine-remQuot : ∀ k i → uncurry combine (remQuot k i) ≡ i
  *↔× : Fin (m * n) ↔ (Fin m × Fin n)
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
  x∈p⇒∣p-x∣<∣p∣   : x ∈ p → ∣ p - x ∣ < ∣ p ∣
  x∈p∧x≢y⇒x∈p-y   : x ∈ p → x ≢ y → x ∈ p - y
  ```

* Added new proofs to `Data.Nat.Properties`:
  ```agda
  >⇒≢ : _>_ ⇒ _≢_

  pred[n]≤n : pred n ≤ n

  n<1⇒n≡0 : n < 1 → n ≡ 0
  m<n⇒0<n : m < n → 0 < n

  m≤n*m : 0 < n → m ≤ n * m
  
  ≤-isTotalPreorder         : IsTotalPreorder _≡_ _≤_
  ≤-totalPreorder           : TotalPreorder 0ℓ 0ℓ 0ℓ

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

* Added new relation to `Data.Integer.Base`:
  ```agda
  _≤ᵇ_ : ℤ → ℤ → Bool
  ```

* Added new proofs to `Data.Integer.Properties`:
  ```agda
  ≤-isTotalPreorder         : IsTotalPreorder _≡_ _≤_
  ≤-totalPreorder           : TotalPreorder 0ℓ 0ℓ 0ℓ
  
  ≤ᵇ⇒≤                      : T (i ≤ᵇ j) → i ≤ j
  ≤⇒≤ᵇ                      : i ≤ j → T (i ≤ᵇ j)

  m*n≡0⇒m≡0∨n≡0             : m * n ≡ 0ℤ → m ≡ 0ℤ ⊎ n ≡ 0ℤ

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

* Added new proofs to `Data.List.Relation.Binary.Pointwise`:
  ```agda
  foldr⁺  : (R w x → R y z → R (w • y) (x ◦ z)) → 
            R e f → Pointwise R xs ys → R (foldr _•_ e xs) (foldr _◦_ f ys)
  lookup⁻ : length xs ≡ length ys →
            (toℕ i ≡ toℕ j → R (lookup xs i) (lookup ys j)) →
            Pointwise R xs ys
  lookup⁺ : (Rxys : Pointwise R xs ys) →
            ∀ i → (let j = cast (Pointwise-length Rxys) i) →
            R (lookup xs i) (lookup ys j)
  ```

* Added new proof to `Data.List.Relation.Unary.All.Properties`:
  ```agda
  all-upTo : All (_< n) (upTo n)
  ```

* Added new proof to `Data.List.Relation.Binary.Equality.Setoid`:
  ```agda
  foldr⁺ : (w ≈ x → y ≈ z → (w • y) ≈ (x ◦ z)) →
           e ≈ f → xs ≋ ys → foldr _•_ e xs ≈ foldr _◦_ f ys
  ```

* Added new proof to `Data.List.Relation.Binary.Subset.Setoid.Properties`:
  ```agda
  applyUpTo⁺ : m ≤ n → applyUpTo f m ⊆ applyUpTo f n
  ```

* Added new proof to `Data.List.Relation.Binary.Subset.Propositional.Properties`:
  ```agda
  applyUpTo⁺ : m ≤ n → applyUpTo f m ⊆ applyUpTo f n
  ```

* Added new proofs in `Data.Rational.Properties`:
  ```agda
  toℚᵘ-homo-1/ : toℚᵘ (1/ p) ℚᵘ.≃ ℚᵘ.1/ (toℚᵘ p)
  *-inverseˡ   : 1/ p * p ≡ 1ℚ
  *-inverseʳ   : p * 1/ p ≡ 1ℚ
  
  positive⇒nonNegative : ∀ {q} → Positive q → NonNegative q
  negative⇒nonPositive : ∀ {q} → Negative q → NonPositive q
  toℚᵘ-mono-< : ∀ {p q} → p < q → toℚᵘ p <ᵘ toℚᵘ q
  toℚᵘ-cancel-< : ∀ {p q} → toℚᵘ p <ᵘ toℚᵘ q → p < q
  toℚᵘ-isOrderHomomorphism-< : IsOrderHomomorphism _≡_ _≃ᵘ_ _<_ _<ᵘ_ toℚᵘ
  toℚᵘ-isOrderMonomorphism-< : IsOrderMonomorphism _≡_ _≃ᵘ_ _<_ _<ᵘ_ toℚᵘ
  neg-distrib-+ : ∀ p q → - (p + q) ≡ (- p) + (- q)
  +-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  +-monoˡ-≤ : ∀ r → (_+ r) Preserves _≤_ ⟶ _≤_
  +-monoʳ-≤ : ∀ r → (_+_ r) Preserves _≤_ ⟶ _≤_
  +-mono-<-≤ : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
  +-mono-< : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
  +-monoˡ-< : ∀ r → (_+ r) Preserves _<_ ⟶ _<_
  +-monoʳ-< : ∀ r → (_+_ r) Preserves _<_ ⟶ _<_
  neg-distribˡ-* : ∀ p q → - (p * q) ≡ - p * q
  neg-distribʳ-* : ∀ p q → - (p * q) ≡ p * - q
  *-monoˡ-≤-nonNeg : ∀ {r} → NonNegative r → (_* r) Preserves _≤_ ⟶ _≤_
  *-monoʳ-≤-nonNeg : ∀ {r} → NonNegative r → (r *_) Preserves _≤_ ⟶ _≤_
  *-monoˡ-≤-pos : ∀ {r} → Positive r → (_* r) Preserves _≤_ ⟶ _≤_
  *-monoʳ-≤-pos : ∀ {r} → Positive r → (r *_) Preserves _≤_ ⟶ _≤_
  *-monoˡ-<-pos : ∀ {r} → Positive r → (_* r) Preserves _<_ ⟶ _<_
  *-monoʳ-<-pos : ∀ {r} → Positive r → (r *_) Preserves _<_ ⟶ _<_
  ```
  
* Add new relations and functions to `Data.Rational.Unnormalised`:
  ```agda
  _≤ᵇ_ : ℤ → ℤ → Bool
  _⊔_  : (p q : ℚᵘ) → ℚᵘ
  _⊓_  : (p q : ℚᵘ) → ℚᵘ
  ∣_∣  : ℚᵘ → ℚᵘ
  ```

* Add new proofs to `Data.Rational.Unnormalised.Properties`:
  ```agda
  /-cong                    : p₁ ≡ p₂ → q₁ ≡ q₂ → p₁ / q₁ ≡ p₂ / q₂
  ↥[p/q]≡p                  : ↥ (p / q) ≡ p
  ↧[p/q]≡q                  : ↧ (p / q) ≡ ℤ.+ q

  ≤-isPreorder              : IsPreorder _≃_ _≤_
  ≤-isPreorder-≡            : IsPreorder _≡_ _≤_
  ≤-isTotalPreorder         : IsTotalPreorder _≃_ _≤_
  ≤-isTotalPreorder-≡       : IsTotalPreorder _≡_ _≤_
  ≤-preorder                : Preorder 0ℓ 0ℓ 0ℓ
  ≤-preorder-≡              : Preorder 0ℓ 0ℓ 0ℓ
  ≤-totalPreorder           : TotalPreorder 0ℓ 0ℓ 0ℓ
  ≤-totalPreorder-≡         : TotalPreorder 0ℓ 0ℓ 0ℓ

  ≤ᵇ⇒≤                      : T (p ≤ᵇ q) → p ≤ q
  ≤⇒≤ᵇ                      : p ≤ q → T (p ≤ᵇ q)

  neg-cancel-<              : - p < - q → q < p
  neg-cancel-≤-≥            : - p ≤ - q → q ≤ p

  mono⇒cong                 : f Preserves _≤_ ⟶ _≤_ → f Preserves _≃_ ⟶ _≃_
  antimono⇒cong             : f Preserves _≤_ ⟶ _≥_ → f Preserves _≃_ ⟶ _≃_

  *-congˡ                   : LeftCongruent _≃_ _*_
  *-congʳ                   : RightCongruent _≃_ _*_

  *-cancelˡ-/               : (ℤ.+ p ℤ.* q) / (p ℕ.* r) ≃ q / r
  *-cancelʳ-/               : (q ℤ.* ℤ.+ p) / (r ℕ.* p) ≃ q / r

  *-cancelʳ-≤-neg           : Negative r → p * r ≤ q * r → q ≤ p
  *-cancelˡ-≤-neg           : Negative r → r * p ≤ r * q → q ≤ p
  *-monoˡ-≤-nonPos          : NonPositive r → (_* r) Preserves _≤_ ⟶ _≥_
  *-monoʳ-≤-nonPos          : NonPositive r → (r *_) Preserves _≤_ ⟶ _≥_
  *-monoˡ-≤-neg             : Negative r → (_* r) Preserves _≤_ ⟶ _≥_
  *-monoʳ-≤-neg             : Negative r → (r *_) Preserves _≤_ ⟶ _≥_

  *-cancelˡ-<-pos           : Positive r → r * p < r * q → p < q
  *-cancelʳ-<-pos           : Positive r → p * r < q * r → p < q
  *-monoˡ-<-neg             : Negative r → (_* r) Preserves _<_ ⟶ _>_
  *-monoʳ-<-neg             : Negative r → (r *_) Preserves _<_ ⟶ _>_
  *-cancelˡ-<-nonPos        : NonPositive r → r * p < r * q → q < p
  *-cancelʳ-<-nonPos        : NonPositive r → p * r < q * r → q < p
  *-cancelˡ-<-neg           : Negative r → r * p < r * q → q < p
  *-cancelʳ-<-neg           : Negative r → p * r < q * r → q < p

  positive⇒1/positive       : Positive q → Positive (1/ q)
  negative⇒1/negative       : Negative q → Negative (1/ q)
  1/-involutive-≡           : 1/ (1/ q) ≡ q
  1/-involutive             : 1/ (1/ q) ≃ q
  p>1⇒1/p<1                 : p > 1ℚᵘ → (1/ p) < 1ℚᵘ

  ⊓-congˡ                   : LeftCongruent _≃_ _⊓_
  ⊓-congʳ                   : RightCongruent _≃_ _⊓_
  ⊓-cong                    : Congruent₂ _≃_ _⊓_
  ⊓-idem                    : Idempotent _≃_ _⊓_
  ⊓-sel                     : Selective _≃_ _⊓_
  ⊓-assoc                   : Associative _≃_ _⊓_
  ⊓-comm                    : Commutative _≃_ _⊓_

  ⊔-congˡ                   : LeftCongruent _≃_ _⊔_
  ⊔-congʳ                   : RightCongruent _≃_ _⊔_
  ⊔-cong                    : Congruent₂ _≃_ _⊔_
  ⊔-idem                    : Idempotent _≃_ _⊔_
  ⊔-sel                     : Selective _≃_ _⊔_
  ⊔-assoc                   : Associative _≃_ _⊔_
  ⊔-comm                    : Commutative _≃_ _⊔_

  ⊓-distribˡ-⊔              : _DistributesOverˡ_ _≃_ _⊓_ _⊔_
  ⊓-distribʳ-⊔              : _DistributesOverʳ_ _≃_ _⊓_ _⊔_
  ⊓-distrib-⊔               : _DistributesOver_  _≃_ _⊓_ _⊔_
  ⊔-distribˡ-⊓              : _DistributesOverˡ_ _≃_ _⊔_ _⊓_
  ⊔-distribʳ-⊓              : _DistributesOverʳ_ _≃_ _⊔_ _⊓_
  ⊔-distrib-⊓               : _DistributesOver_  _≃_ _⊔_ _⊓_
  ⊓-absorbs-⊔               : _Absorbs_ _≃_ _⊓_ _⊔_ 
  ⊔-absorbs-⊓               : _Absorbs_ _≃_ _⊔_ _⊓_ 
  ⊔-⊓-absorptive            : Absorptive _≃_ _⊔_ _⊓_
  ⊓-⊔-absorptive            : Absorptive _≃_ _⊓_ _⊔_

  ⊓-isMagma                 : IsMagma _≃_ _⊓_
  ⊓-isSemigroup             : IsSemigroup _≃_ _⊓_
  ⊓-isCommutativeSemigroup  : IsCommutativeSemigroup _≃_ _⊓_
  ⊓-isBand                  : IsBand _≃_ _⊓_
  ⊓-isSemilattice           : IsSemilattice _≃_ _⊓_
  ⊓-isSelectiveMagma        : IsSelectiveMagma _≃_ _⊓_

  ⊔-isMagma                 : IsMagma _≃_ _⊔_
  ⊔-isSemigroup             : IsSemigroup _≃_ _⊔_
  ⊔-isCommutativeSemigroup  : IsCommutativeSemigroup _≃_ _⊔_
  ⊔-isBand                  : IsBand _≃_ _⊔_
  ⊔-isSemilattice           : IsSemilattice _≃_ _⊔_
  ⊔-isSelectiveMagma        : IsSelectiveMagma _≃_ _⊔_

  ⊔-⊓-isLattice             : IsLattice _≃_ _⊔_ _⊓_
  ⊓-⊔-isLattice             : IsLattice _≃_ _⊓_ _⊔_
  ⊔-⊓-isDistributiveLattice : IsDistributiveLattice _≃_ _⊔_ _⊓_
  ⊓-⊔-isDistributiveLattice : IsDistributiveLattice _≃_ _⊓_ _⊔_

  ⊓-rawMagma                : RawMagma _ _
  ⊔-rawMagma                : RawMagma _ _
  ⊔-⊓-rawLattice            : RawLattice _ _

  ⊓-magma                   : Magma _ _
  ⊓-semigroup               : Semigroup _ _
  ⊓-band                    : Band _ _
  ⊓-commutativeSemigroup    : CommutativeSemigroup _ _
  ⊓-semilattice             : Semilattice _ _
  ⊓-selectiveMagma          : SelectiveMagma _ _

  ⊔-magma                   : Magma _ _
  ⊔-semigroup               : Semigroup _ _
  ⊔-band                    : Band _ _
  ⊔-commutativeSemigroup    : CommutativeSemigroup _ _
  ⊔-semilattice             : Semilattice _ _
  ⊔-selectiveMagma          : SelectiveMagma _ _

  ⊔-⊓-lattice               : Lattice _ _
  ⊓-⊔-lattice               : Lattice _ _
  ⊔-⊓-distributiveLattice   : DistributiveLattice _ _
  ⊓-⊔-distributiveLattice   : DistributiveLattice _ _

  ⊓-triangulate             : p ⊓ q ⊓ r ≃ (p ⊓ q) ⊓ (q ⊓ r)
  ⊔-triangulate             : p ⊔ q ⊔ r ≃ (p ⊔ q) ⊔ (q ⊔ r)

  ⊓-glb                     : m ≥ o → n ≥ o → m ⊓ n ≥ o
  ⊓-mono-≤                  : _⊓_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ⊓-monoˡ-≤                 : (_⊓ n) Preserves _≤_ ⟶ _≤_
  ⊓-monoʳ-≤                 : (n ⊓_) Preserves _≤_ ⟶ _≤_

  ⊔-lub                     : m ≤ o → n ≤ o → m ⊔ n ≤ o
  ⊔-mono-≤                  : _⊔_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ⊔-monoˡ-≤                 : (_⊔ n) Preserves _≤_ ⟶ _≤_
  ⊔-monoʳ-≤                 : (n ⊔_) Preserves _≤_ ⟶ _≤_
 
  p⊓q≃q⇒q≤p                 : p ⊓ q ≃ q → q ≤ p
  p⊓q≃p⇒p≤q                 : p ⊓ q ≃ p → p ≤ q
  p⊔q≃q⇒p≤q                 : p ⊔ q ≃ q → p ≤ q
  p⊔q≃p⇒q≤p                 : p ⊔ q ≃ p → q ≤ p

  p⊓q≤p                     : p ⊓ q ≤ p
  p⊓q≤q                     : p ⊓ q ≤ q
  p≤q⇒p⊓r≤q                 : p ≤ q → p ⊓ r ≤ q
  p≤q⇒r⊓p≤q                 : p ≤ q → r ⊓ p ≤ q
  p≤q⊓r⇒p≤q                 : p ≤ q ⊓ r → p ≤ q
  p≤q⊓r⇒p≤r                 : p ≤ q ⊓ r → p ≤ r

  p≤p⊔q                     : p ≤ p ⊔ q
  p≤q⊔p                     : p ≤ q ⊔ p
  p≤q⇒p≤q⊔r                 : p ≤ q → p ≤ q ⊔ r
  p≤q⇒p≤r⊔q                 : p ≤ q → p ≤ r ⊔ q
  p⊔q≤r⇒p≤r                 : p ⊔ q ≤ r → p ≤ r
  p⊔q≤r⇒q≤r                 : p ⊔ q ≤ r → q ≤ r
  
  p≤q⇒p⊔q≃q                 : p ≤ q → p ⊔ q ≃ q
  p≥q⇒p⊔q≃p                 : p ≥ q → p ⊔ q ≃ p
  p≤q⇒p⊓q≃p                 : p ≤ q → p ⊓ q ≃ p
  p≥q⇒p⊓q≃q                 : p ≥ q → p ⊓ q ≃ q
  p⊓q≤p⊔q                   : p ⊓ q ≤ p ⊔ q

  mono-≤-distrib-⊔          : f Preserves _≤_ ⟶ _≤_ → f (m ⊔ n) ≃ f m ⊔ f n
  mono-≤-distrib-⊓          : f Preserves _≤_ ⟶ _≤_ → f (m ⊓ n) ≃ f m ⊓ f n
  antimono-≤-distrib-⊓      : f Preserves _≤_ ⟶ _≥_ → f (m ⊓ n) ≃ f m ⊔ f n
  antimono-≤-distrib-⊔      : f Preserves _≤_ ⟶ _≥_ → f (m ⊔ n) ≃ f m ⊓ f n

  neg-distrib-⊔-⊓           : - (p ⊔ q) ≃ - p ⊓ - q
  neg-distrib-⊓-⊔           : - (p ⊓ q) ≃ - p ⊔ - q

  *-distribˡ-⊓-nonNeg       : NonNegative p → p * (q ⊓ r) ≃ (p * q) ⊓ (p * r)
  *-distribʳ-⊓-nonNeg       : NonNegative p → (q ⊓ r) * p ≃ (q * p) ⊓ (r * p)
  *-distribˡ-⊔-nonNeg       : NonNegative p → p * (q ⊔ r) ≃ (p * q) ⊔ (p * r)
  *-distribʳ-⊔-nonNeg       : NonNegative p → (q ⊔ r) * p ≃ (q * p) ⊔ (r * p)
  *-distribˡ-⊔-nonPos       : NonPositive p → p * (q ⊔ r) ≃ (p * q) ⊓ (p * r)
  *-distribʳ-⊔-nonPos       : NonPositive p → (q ⊔ r) * p ≃ (q * p) ⊓ (r * p)
  *-distribˡ-⊓-nonPos       : NonPositive p → p * (q ⊓ r) ≃ (p * q) ⊔ (p * r)
  *-distribʳ-⊓-nonPos       : NonPositive p → (q ⊓ r) * p ≃ (q * p) ⊔ (r * p)

  ∣_∣-cong                  : p ≃ q → ∣ p ∣ ≃ ∣ q ∣
  ∣p∣≃0⇒p≃0                 : ∣ p ∣ ≃ 0ℚᵘ → p ≃ 0ℚᵘ
  ∣-p∣≡∣p∣                  : ∣ - p ∣ ≡ ∣ p ∣
  ∣-p∣≃∣p∣                  : ∣ - p ∣ ≃ ∣ p ∣
  0≤p⇒∣p∣≡p                 : 0ℚᵘ ≤ p → ∣ p ∣ ≡ p
  0≤p⇒∣p∣≃p                 : 0ℚᵘ ≤ p → ∣ p ∣ ≃ p
  ∣p∣≡p⇒0≤p                 : ∣ p ∣ ≡ p → 0ℚᵘ ≤ p
  ∣p∣≡p∨∣p∣≡-p              : (∣ p ∣ ≡ p) ⊎ (∣ p ∣ ≡ - p)
  ∣p+q∣≤∣p∣+∣q∣             : ∣ p + q ∣ ≤ ∣ p ∣ + ∣ q ∣
  ∣p-q∣≤∣p∣+∣q∣             : ∣ p - q ∣ ≤ ∣ p ∣ + ∣ q ∣
  ∣p*q∣≡∣p∣*∣q∣             : ∣ p * q ∣ ≡ ∣ p ∣ * ∣ q ∣
  ∣p*q∣≃∣p∣*∣q∣             : ∣ p * q ∣ ≃ ∣ p ∣ * ∣ q ∣
  ```

* Added new definitions to `IO`:
  ```agda
  getLine : IO String
  Main : Set
  ```

* Added new definitions to `Relation.Binary.Bundles`:
  ```agda
  record TotalPreorder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂))
  ```

* Added new definitions to `Relation.Binary.Structures`:
  ```agda
  record IsTotalPreorder (_≲_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂)
  ```

* Added new proofs to `Relation.Binary.Properties.Poset`:
  ```agda
  mono⇒cong     : f Preserves _≤_ ⟶ _≤_ → f Preserves _≈_ ⟶ _≈_
  antimono⇒cong : f Preserves _≤_ ⟶ _≥_ → f Preserves _≈_ ⟶ _≈_
  ```

* Added new proofs to `Relation.Binary.Consequences`:
  ```agda
  mono⇒cong     : Symmetric _≈_ → _≈_ ⇒ _≤_ → Antisymmetric _≈_ _≤_ → f Preserves _≤_ ⟶ _≤_ → f Preserves _≈_ ⟶ _≈_
  antimono⇒cong : Symmetric _≈_ → _≈_ ⇒ _≤_ → Antisymmetric _≈_ _≤_ → f Preserves _≤_ ⟶ (flip _≤_) → f Preserves _≈_ ⟶ _≈_
  ```

* Added new proofs to `Relation.Binary.Construct.Converse`:
  ```agda
  totalPreorder   : TotalPreorder a ℓ₁ ℓ₂ → TotalPreorder a ℓ₁ ℓ₂
  isTotalPreorder : IsTotalPreorder ≈ ∼  → IsTotalPreorder ≈ (flip ∼)
  ```
