Version TODO
============

The library has been tested using Agda version 2.5.4.1.

Important changes since 0.17:

Non-backwards compatible changes
--------------------------------

#### Overhaul of `Data.Maybe`

Splitting up `Data.Maybe` into the standard hierarchy.

* Moved `Data.Maybe.Base`'s `Is-just`, `Is-nothing`, `to-witness`,
  and `to-witness-T` to `Data.Maybe` (they rely on `All` and `Any`
  which are now outside of `Data.Maybe.Base`).

* Moved `Data.Maybe.Base`'s `All` and `Data.Maybe`'s `allDec` to
  `Data.Maybe.All` and renamed some proofs:
  ```agda
  allDec ↦ dec
  ```

* Moved `Data.Maybe.Base`'s `Any` and `Data.Maybe`'s `anyDec` to
  `Data.Maybe.Any` and renamed some proofs:
  ```agda
  anyDec ↦ dec
  ```

* Created `Data.Maybe.Properties`, moved `Data.Maybe.Base`'s `just-injective`
  there and populated it with basic results.

* Moved `Data.Maybe`'s `Eq` to `Data.Maybe.Relation.Pointwise` and
  renamed some proofs:
  ```agda
  Eq                  ↦ Pointwise
  Eq-refl             ↦ refl
  Eq-sym              ↦ sym
  Eq-trans            ↦ trans
  Eq-dec              ↦ dec
  Eq-isEquivalence    ↦ isEquivalence
  Eq-isDecEquivalence ↦ isDecEquivalence
  ```

Other major changes
-------------------

* Added new modules `Data.Integer.Divisibility.Properties`,
  and `Data.Integer.DivMod`.

* Added new module `Relation.Binary.StrictPartialOrderReasoning`

Deprecated features
-------------------

Other minor additions
---------------------

* Added new type to `Data.Integer.Divisibility`
  ```agda
  record k ∣′ z = (quotient : ℤ) ** (z ≡ quotient * k)
  ```

* Added new proofs to `Data.Integer.Properties`:
  ```agda
  suc-pred   : sucℤ (pred m) ≡ m
  pred-suc   : pred (sucℤ m) ≡ m
  neg-suc    : - + suc m ≡ pred (- + m)
  suc-+      : + suc m + n ≡ sucℤ (+ m + n)
  +-pred     : m + pred n ≡ pred (m + n)
  pred-+     : pred m + n ≡ pred (m + n)
  minus-suc  : m - + suc n ≡ pred (m - + n)
  sm*n≡n+m*n : sucℤ m * n ≡ n + m * n

  ⊓-comm    : Commutative _⊓_
  ⊓-assoc   : Associative _⊓_
  ⊓-idem    : Idempotent _⊓_
  ⊓-sel     : Selective _⊓_
  m≤n⇒m⊓n≡m : m ≤ n → m ⊓ n ≡ m
  m⊓n≡m⇒m≤n : m ⊓ n ≡ m → m ≤ n
  m≥n⇒m⊓n≡n : m ≥ n → m ⊓ n ≡ n
  m⊓n≡n⇒m≥n : m ⊓ n ≡ n → m ≥ n
  m⊓n≤n     : m ⊓ n ≤ n
  m⊓n≤m     : m ⊓ n ≤ m

  ⊔-comm    : Commutative _⊔_
  ⊔-assoc   : Associative _⊔_
  ⊔-idem    : Idempotent _⊔_
  ⊔-sel     : Selective _⊔_
  m≤n⇒m⊔n≡n : m ≤ n → m ⊔ n ≡ n
  m⊔n≡n⇒m≤n : m ⊔ n ≡ n → m ≤ n
  m≥n⇒m⊔n≡m : m ≥ n → m ⊔ n ≡ m
  m⊔n≡m⇒m≥n : m ⊔ n ≡ m → m ≥ n
  m≤m⊔n     : m ≤ m ⊔ n
  n≤m⊔n     : n ≤ m ⊔ n

  neg-distrib-⊔-⊓ : - (m ⊔ n) ≡ - m ⊓ - n
  neg-distrib-⊓-⊔ : - (m ⊓ n) ≡ - m ⊔ - n

  pred-mono         : pred Preserves _≤_ ⟶ _≤_
  suc-mono          : sucℤ Preserves _≤_ ⟶ _≤_
  ⊖-monoʳ-≥-≤       : (p ⊖_) Preserves ℕ._≥_ ⟶ _≤_
  ⊖-monoˡ-≤         : (_⊖ p) Preserves ℕ._≤_ ⟶ _≤_
  +-monoʳ-≤         : (_+_ n) Preserves _≤_ ⟶ _≤_
  +-monoˡ-≤         : (_+ n) Preserves _≤_ ⟶ _≤_
  +-monoˡ-<         : (_+ n) Preserves _<_ ⟶ _<_
  +-monoʳ-<         : (_+_ n) Preserves _<_ ⟶ _<_
  *-monoˡ-≤-pos     : (+ suc n *_) Preserves _≤_ ⟶ _≤_
  *-monoʳ-≤-non-neg : (_* + n) Preserves _≤_ ⟶ _≤
  *-monoˡ-≤-non-neg : (+ n *_) Preserves _≤_ ⟶ _≤_
  +-mono-≤          : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  +-mono-<          : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
  +-mono-≤-<        : _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
  +-mono-<-≤        : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
  neg-mono-≤-≥      : -_ Preserves _≤_ ⟶ _≥_
  neg-mono-<->      : -_ Preserves _<_ ⟶ _>_

  *-cancelˡ-≡     : i ≢ + 0 → i * j ≡ i * k → j ≡ k
  *-cancelˡ-≤-pos : + suc m * n ≤ + suc m * o → n ≤ o

  neg-≤-pos     : - (+ m) ≤ + n
  0⊖m≤+         : 0 ⊖ m ≤ + n
  m≤n⇒m-n≤0     : m ≤ n → m - n ≤ + 0
  m-n≤0⇒m≤n     : m - n ≤ + 0 → m ≤ n
  m≤n⇒0≤n-m     : m ≤ n → + 0 ≤ n - m
  0≤n-m⇒m≤n     : + 0 ≤ n - m → m ≤ n
  m≤pred[n]⇒m<n : m ≤ pred n → m < n
  m<n⇒m≤pred[n] : m < n → m ≤ pred n
  m≤m+n         : m ≤ m + + n
  n≤m+n         : n ≤ + m + n
  m-n≤m         : m - + n ≤ m

  ≤-<-trans : Trans _≤_ _<_ _<_
  <-≤-trans : Trans _<_ _≤_ _<_
  >→≰       : x > y → x ≰ y
  >-irrefl  : Irreflexive _≡_ _>_

  <-isStrictPartialOrder : IsStrictPartialOrder _≡_ _<_
  <-strictPartialOrder   : StrictPartialOrder _ _ _

  pos-+-commute  : Homomorphic₂ +_ ℕ._+_ _+_
  neg-distribˡ-* : - (x * y) ≡ (- x) * y
  neg-distribʳ-* : - (x * y) ≡ x * (- y)
  *-distribˡ-+   : _*_ DistributesOverˡ _+_
  ≤-steps        : m ≤ n → m ≤ + p + n
  ≤-step-neg     : m ≤ n → pred m ≤ n
  ≤-steps-neg    : m ≤ n → m - + p ≤ n
  m≡n⇒m-n≡0      : m ≡ n → m - n ≡ + 0
  m-n≡0⇒m≡n      : m - n ≡ + 0 → m ≡ n
  0≤n⇒+∣n∣≡n     : + 0 ≤ n → + ∣ n ∣ ≡ n
  +∣n∣≡n⇒0≤n     : + ∣ n ∣ ≡ n → + 0 ≤ n
  ◃-≡            : sign m ≡ sign n → ∣ m ∣ ≡ ∣ n ∣ → m ≡ n

  +-*-ring : Ring _ _
  ```

* Added new operations to `Data.List.All`:
  ```agda
  zipWith   : P ∩ Q ⊆ R → All P ∩ All Q ⊆ All R
  unzipWith : R ⊆ P ∩ Q → All R ⊆ All P ∩ All Q

  sequenceA : All (F ∘′ P) ⊆ F ∘′ All P
  sequenceM : All (M ∘′ P) ⊆ M ∘′ All P
  mapA      : (Q ⊆ F ∘′ P) → All Q ⊆ (F ∘′ All P)
  mapM      : (Q ⊆ M ∘′ P) → All Q ⊆ (M ∘′ All P)
  forA      : All Q xs → (Q ⊆ F ∘′ P) → F (All P xs)
  forM      : All Q xs → (Q ⊆ M ∘′ P) → M (All P xs)
  ```

* Added new proofs to `Data.List.All.Properties`:
  ```agda
  respects : P Respects _≈_ → (All P) Respects _≋_
  ```

* Added new proofs to `Data.Maybe.All`:
  ```agda
  drop-just        : All P (just x) → P x
  just-equivalence : P x ⇔ All P (just x)
  map              : P ⊆ Q → All P ⊆ All Q
  fromAny          : Any P ⊆ All P
  zipWith          : P ∩ Q ⊆ R → All P ∩ All Q ⊆ All R
  unzipWith        : P ⊆ Q ∩ R → All P ⊆ All Q ∩ All R
  zip              : All P ∩ All Q ⊆ All (P ∩ Q)
  unzip            : All (P ∩ Q) ⊆ All P ∩ All Q
  sequenceA        : RawApplicative F → All (F ∘′ P) ⊆ F ∘′ All P
  mapA             : RawApplicative F → (Q ⊆ F ∘′ P) → All Q ⊆ (F ∘′ All P)
  forA             : RawApplicative F → All Q xs → (Q ⊆ F ∘′ P) → F (All P xs)
  sequenceM        : RawMonad M → All (M ∘′ P) ⊆ M ∘′ All P
  mapM             : RawMonad M → (Q ⊆ M ∘′ P) → All Q ⊆ (M ∘′ All P)
  forM             : RawMonad M → All Q xs → (Q ⊆ M ∘′ P) → M (All P xs)
  universal        : Universal P → Universal (All P)
  irrelevant       : Irrelevant P → Irrelevant (All P)
  satisfiable      : Satisfiable (All P)
  ```

* Created `Data.Maybe.All.Properties`:
  ```agda
  map⁺ : All (P ∘ f) mx → All P (map f mx)
  map⁻ : All P (map f mx) → All (P ∘ f) mx
  gmap : P ⊆ Q ∘ f → All P ⊆ All Q ∘ map f
  <∣>⁺ : All P mx → All P my → All P (mx <∣> my)
  <∣>⁻ : All P (mx <∣> my) → All P mx
  ```

* Added new proofs to `Data.Maybe.Any`:
  ```agda
  drop-just        : Any P (just x) → P x
  just-equivalence : P x ⇔ Any P (just x)
  map              : P ⊆ Q → Any P ⊆ Any Q
  satisfied        : Any P x → ∃ P
  zipWith          : P ∩ Q ⊆ R → Any P ∩ Any Q ⊆ Any R
  unzipWith        : P ⊆ Q ∩ R → Any P ⊆ Any Q ∩ Any R
  zip              : Any P ∩ Any Q ⊆ Any (P ∩ Q)
  unzip            : Any (P ∩ Q) ⊆ Any P ∩ Any Q
  irrelevant       : Irrelevant P → Irrelevant (Any P)
  satisfiable      : Satisfiable P → Satisfiable (Any P)
  ```

* Added new function to `Data.Maybe.Base`:
  ```agda
  _<∣>_     : Maybe A → Maybe A → Maybe A
  ```
