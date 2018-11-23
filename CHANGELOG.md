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
  there and added new results.

* Moved `Data.Maybe`'s `Eq` to `Data.Maybe.Relation.Pointwise`, made the
  relation heterogeneously typed and renamed the following proofs:
  ```agda
  Eq                  ↦ Pointwise
  Eq-refl             ↦ refl
  Eq-sym              ↦ sym
  Eq-trans            ↦ trans
  Eq-dec              ↦ dec
  Eq-isEquivalence    ↦ isEquivalence
  Eq-isDecEquivalence ↦ isDecEquivalence
  ```

#### Changes to the algebra hierarchy

* Added `Magma` and `IsMagma` to the algebra hierarchy.

* The name `RawSemigroup` in `Algebra` has been deprecated in favour of `RawMagma`.

#### Relaxation of ring solvers requirements

* In the ring solvers below, the assumption that equality is `Decidable`
  has been replaced by a strictly weaker assumption that it is `WeaklyDecidable`.
  This allows the solvers to be used when equality is not fully decidable.
  ```
  Algebra.Solver.Ring
  Algebra.Solver.Ring.NaturalCoefficients
  ```

* Created a module `Algebra.Solver.Ring.NaturalCoefficients.Default` that
  instantiates the solver for any `CommutativeSemiring`.

#### Other

* The proof `sel⇒idem` has been moved from `Algebra.FunctionProperties.Consequences` to
  `Algebra.FunctionProperties.Consequences.Propositional` as it does not rely on equality.

* Moved `_≟_` from `Data.Bool.Base` to `Data.Bool.Properties`. Backwards
  compatibility has been (nearly completely) preserved by having `Data.Bool`
  publicly re-export `_≟_`.

* In `Data.List.Membership.Propositional.Properties`:
    - Made the `Set` argument implicit in `∈-++⁺ˡ`, `∈-++⁺ʳ`, `∈-++⁻`, `∈-insert`, `∈-∃++`.
    - Made the `A → B` argument explicit in `∈-map⁺`, `∈-map⁻`, `map-∈↔`.

Other major changes
-------------------

* Added new module `Algebra.FunctionProperties.Consequences.Propositional`

* Added new module `Codata.Cowriter`

* Added new modules `Codata.M.Properties` and `Codata.M.Bisimilarity`

* Added new modules `Data.List.First` and `Data.List.First.Properties` for a
  generalization of the notion of "first element in the list to satisfy a
  predicate".

* Added new module `Data.Vec.Any.Properties`

* Added new module `Relation.Binary.Properties.BoundedLattice`

Deprecated features
-------------------

Other minor additions
---------------------

* Added new records to `Algebra`:
  ```agda
  record RawMagma c ℓ : Set (suc (c ⊔ ℓ))
  record Magma    c ℓ : Set (suc (c ⊔ ℓ))
  ```

* Added new proof to `Algebra.FunctionProperties.Consequences`:
  ```agda
  wlog : Commutative f → Total _R_ → (∀ a b → a R b → P (f a b)) → ∀ a b → P (f a b)
  ```

* Added new operator to `Algebra.Solver.Ring`.
  ```agda
  _:×_
  ```

* Added new records to `Algebra.Structures`:
  ```agda
  record IsMagma (∙ : Op₂ A) : Set (a ⊔ ℓ)
  ```

* Added new functions to `Codata.Colist`:
  ```agda
  fromCowriter : Cowriter W A i → Colist W i
  toCowriter   : Colist A i → Cowriter A ⊤ i
  [_]          : A → Colist A ∞
  chunksOf     : (n : ℕ) → Colist A ∞ → Cowriter (Vec A n) (BoundedVec A n) ∞
  ```

* Added new functions to `Codata.Stream`:
  ```agda
  splitAt    : (n : ℕ) → Stream A ∞ → Vec A n × Stream A ∞
  drop       : ℕ → Stream A ∞ → Stream A ∞
  interleave : Stream A i → Thunk (Stream A) i → Stream A i
  chunksOf   : (n : ℕ) → Stream A ∞ → Stream (Vec A n) ∞
  ```

* Added new proof to `Codata.Stream.Properties`:
  ```agda
  splitAt-map : splitAt n (map f xs) ≡ map (map f) (map f) (splitAt n xs)
  ```

* Added new function to `Data.Fin.Base`:
  ```agda
  cast : m ≡ n → Fin m → Fin n
  ```

<<<<<<< HEAD
* Added new proof to `Data.Fin.Properties`:
=======
* Added new proofs to `Data.List.Any.Properties`:
  ```agda
  here-injective  : here  p ≡ here  q → p ≡ q
  there-injective : there p ≡ there q → p ≡ q

  singleton⁺      : P x → Any P [ x ]
  singleton⁻      : Any P [ x ] → P x
  ++-insert       : P x → Any P (xs ++ [ x ] ++ ys)
  ```

* Added new functions to `Data.List.Base`:
  ```agda
  uncons      : List A → Maybe (A × List A)
  head        : List A → Maybe A
  tail        : List A → Maybe (List A)
  alignWith   : (These A B → C) → List A → List B → List C
  unalignWith : (A → These B C) → List A → List B × List C
  align       : List A → List B → List (These A B)
  unalign     : List (These A B) → List A × List B
  ```

* Added new functions to `Data.List.Categorical`:
  ```agda
  functor     : RawFunctor List
  applicative : RawApplicative List
  monadT      : RawMonadT (_∘′ List)
  sequenceA   : RawApplicative F → List (F A) → F (List A)
  mapA        : RawApplicative F → (A → F B) → List A → F (List B)
  forA        : RawApplicative F → List A → (A → F B) → F (List B)
  forM        : RawMonad M → List A → (A → M B) → M (List B)
  ```

* Added new proofs to `Data.List.Membership.(Setoid/Propositional).Properties`:
  ```agda
  ∈-insert : v ≈ v′ → v ∈ xs ++ [ v′ ] ++ ys
  ∈-∃++    : v ∈ xs → ∃₂ λ ys zs → ∃ λ w → v ≈ w × xs ≋ ys ++ [ w ] ++ zs
  ```

* Added new functions to `Data.List.NonEmpty`:
  ```agda
  uncons      : List⁺ A → A × List A
  concatMap   : (A → List⁺ B) → List⁺ A → List⁺ B
  alignWith   : (These A B → C) → List⁺ A → List⁺ B → List⁺ C
  zipWith     : (A → B → C) → List⁺ A → List⁺ B → List⁺ C
  unalignWith : (A → These B C) → List⁺ A → These (List⁺ B) (List⁺ C)
  unzipWith   : (A → B × C) → List⁺ A → List⁺ B × List⁺ C
  align       : List⁺ A → List⁺ B → List⁺ (These A B)
  zip         : List⁺ A → List⁺ B → List⁺ (A × B)
  unalign     : List⁺ (These A B) → These (List⁺ A) (List⁺ B)
  unzip       : List⁺ (A × B) → List⁺ A × List⁺ B
  ```

* Added new functions to `Data.List.Properties`:
  ```agda
  alignWith-cong        : f ≗ g → alignWith f as ≗ alignWith g as
  length-alignWith      : length (alignWith f xs ys) ≡ length xs ⊔ length ys
  alignWith-map         : alignWith f (map g xs) (map h ys) ≡ alignWith (f ∘′ These.map g h) xs ys
  map-alignWith         : map g (alignWith f xs ys) ≡ alignWith (g ∘′ f) xs ys
  unalignWith-this      : unalignWith this ≗ (_, [])
  unalignWith-that      : unalignWith that ≗ ([] ,_)
  unalignWith-cong      : f ≗ g → unalignWith f ≗ unalignWith g
  unalignWith-map       : unalignWith f (map g ds) ≡ unalignWith (f ∘′ g) ds
  map-unalignWith       : Prod.map (map g) (map h) ∘′ unalignWith f ≗ unalignWith (These.map g h ∘′ f)
  unalignWith-alignWith : f ∘′ g ≗ id → unalignWith f (alignWith g as bs) ≡ (as , bs)
  ```

* Added new function to `Data.Maybe.Base`:
  ```agda
  fromMaybe : A → Maybe A → A
  alignWith : (These A B → C) → Maybe A → Maybe B → Maybe C
  zipWith   : (A → B → C) → Maybe A → Maybe B → Maybe C
  align     : Maybe A → Maybe B → Maybe (These A B)
  zip       : Maybe A → Maybe B → Maybe (A × B)
  ```

* Added new operator to `Data.Nat.Base`:
  ```agda
  ∣_-_∣ : ℕ → ℕ → ℕ
  ```

* Added new proofs to `Data.Nat.Divisibility`:
  ```agda
  n∣m⇒m%n≡0 : suc n ∣ m → m % (suc n) ≡ 0
  m%n≡0⇒n∣m : m % (suc n) ≡ 0 → suc n ∣ m
  m%n≡0⇔n∣m : m % (suc n) ≡ 0 ⇔ suc n ∣ m
  ```

* Added new operations and proofs to `Data.Nat.DivMod`:
  ```agda
  _%_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ

  a≡a%n+[a/n]*n : a ≡ a % suc n + (a div (suc n)) * suc n
  a%1≡0         : a % 1 ≡ 0
  a%n<n         : a % suc n < suc n
  n%n≡0         : suc n % suc n ≡ 0
  a%n%n≡a%n     : a % suc n % suc n ≡ a % suc n
  [a+n]%n≡a%n   : (a + suc n) % suc n ≡ a % suc n
  [a+kn]%n≡a%n  : (a + k * (suc n)) % suc n ≡ a % suc n
  kn%n≡0        : k * (suc n) % suc n ≡ 0
  %-distribˡ-+  : (a + b) % suc n ≡ (a % suc n + b % suc n) % suc n
  ```

* Added new proofs to `Data.Nat.Properties`:
  ```agda
  _≥?_  : Decidable _≥_
  _>?_  : Decidable _>_
  _≤′?_ : Decidable _≤′_
  _<′?_ : Decidable _<′_
  _≤″?_ : Decidable _≤″_
  _<″?_ : Decidable _<″_
  _≥″?_ : Decidable _≥″_
  _>″?_ : Decidable _>″_

  n≤0⇒n≡0      : n ≤ 0 → n ≡ 0
  m<n⇒n≢0      : m < n → n ≢ 0

  m⊓n≡m⇒m≤n    : m ⊓ n ≡ m → m ≤ n
  m⊓n≡n⇒n≤m    : m ⊓ n ≡ n → n ≤ m
  n⊔m≡m⇒n≤m    : n ⊔ m ≡ m → n ≤ m
  n⊔m≡n⇒m≤n    : n ⊔ m ≡ n → m ≤ n

  *-distribˡ-∸ : _*_ DistributesOverˡ _∸_
  *-distrib-∸  : _*_ DistributesOver _∸_
  ^-*-assoc    : (m ^ n) ^ p ≡ m ^ (n * p)

  ≤-poset                : Poset 0ℓ 0ℓ 0ℓ
  <-resp₂-≡              : _<_ Respects₂ _≡_
  <-isStrictPartialOrder : IsStrictPartialOrder _≡_ _<_
  <-strictPartialOrder   : StrictPartialOrder 0ℓ 0ℓ 0ℓ

  *-+-isSemiring         : IsSemiring _+_ _*_ 0 1

  ⊓-semigroup            : Semigroup 0ℓ 0ℓ
  ⊔-semigroup            : Semigroup 0ℓ 0ℓ
  ⊔-0-commutativeMonoid  : CommutativeMonoid 0ℓ 0ℓ
  ⊓-⊔-lattice            : Lattice 0ℓ 0ℓ

  n≡m⇒∣n-m∣≡0       : n ≡ m → ∣ n - m ∣ ≡ 0
  m≤n⇒∣n-m∣≡n∸m     : m ≤ n → ∣ n - m ∣ ≡ n ∸ m
  ∣n-m∣≡0⇒n≡m       : ∣ n - m ∣ ≡ 0 → n ≡ m
  ∣n-m∣≡n∸m⇒m≤n     : ∣ n - m ∣ ≡ n ∸ m → m ≤ n
  ∣n-n∣≡0           : ∣ n - n ∣ ≡ 0
  ∣n-n+m∣≡m         : ∣ n - n + m ∣ ≡ m
  ∣n+m-n+o∣≡∣m-o|   : ∣ n + m - n + o ∣ ≡ ∣ m - o ∣
  n∸m≤∣n-m∣         : n ∸ m ≤ ∣ n - m ∣
  ∣n-m∣≤n⊔m         : ∣ n - m ∣ ≤ n ⊔ m
  ∣-∣-comm          : Commutative ∣_-_∣
  ∣n-m∣≡[n∸m]∨[m∸n] : (∣ n - m ∣ ≡ n ∸ m) ⊎ (∣ n - m ∣ ≡ m ∸ n)
  *-distribˡ-∣-∣    : _*_ DistributesOverˡ ∣_-_∣
  *-distribʳ-∣-∣    : _*_ DistributesOverʳ ∣_-_∣
  *-distrib-∣-∣     : _*_ DistributesOver ∣_-_∣
  ```

* Added new function to `Data.String.Base`:
  ```agda
  fromList⁺ : List⁺ Char → String
  ```

* Added new functions to `Data.Sum`:
  ```agda
  map₁ : (A → B) → A ⊎ C → B ⊎ C
  map₂ : (B → C) → A ⊎ B → A ⊎ C
  ```

* Added new functions in `Data.Table.Base`:
  ```agda
  remove  : Fin (suc n) → Table A (suc n) → Table A n
  fromVec : Vec A n → Table A n
  toVec   : Table A n → Vec A n
  ```

* Added new proofs in `Data.Table.Properties`:
  ```agda
  select-lookup  : lookup (select x i t) i ≡ lookup t i
  select-remove  : remove i (select x i t) ≗ replicate {n} x
  remove-permute : remove (π ⟨$⟩ˡ i) (permute π t) ≗ permute (Perm.remove (π ⟨$⟩ˡ i) π) (remove i t)
  ```

* Added new functions to `Data.Vec`:
  ```agda
  alignWith : (These A B → C) → Vec A m → Vec B n → Vec C (m ⊔ n)
  align     : Vec A m → Vec B n → Vec (These A B) (m ⊔ n)
  unzipWith : (A → B × C) → Vec A n → Vec B n × Vec C n
  ```
  A generalization of single point overwrite `_[_]≔_`
  to single-point modification `_[_]%=_`
  (alias with different argument order: `updateAt`):
  ```agda
  _[_]%=_   : Vec A n → Fin n → (A → A) → Vec A n
  updateAt  : Fin n → (A → A) → Vec A n → Vec A n
  ```

* Added new proofs to `Data.Vec.All.Properties`:
  ```agda
  toList⁺   : All P (toList xs) → All P xs
  toList⁻   : All P xs → All P (toList xs)

  fromList⁺ : All P xs → All P (fromList xs)
  fromList⁻ : All P (fromList xs) → All P xs
  ```

* Added new functions to `Data.Vec.Any`:
  ```agda
  head    : ¬ Any P xs → Any P (x ∷ xs) → P x
  toSum   : Any P (x ∷ xs) → P x ⊎ Any P xs
  fromSum : P x ⊎ Any P xs → Any P (x ∷ xs)
  ```

* Added new functions to `Data.Vec.Categorical`:
  ```agda
  sequenceA : RawApplicative F → Vec (F A) n → F (Vec A n)
  mapA      : RawApplicative F → (A → F B) → Vec A n → F (Vec B n)
  forA      : RawApplicative F → Vec A n → (A → F B) → F (Vec B n)
  sequenceM : RawMonad M → Vec (M A) n → M (Vec A n)
  mapM      : RawMonad M → (A → M B) → Vec A n → M (Vec B n)
  forM      : RawMonad M → Vec A n → (A → M B) → M (Vec B n)
  ```

* Added new proofs to `Data.Vec.Membership.Propositional.Properties`:
  ```agda
  ∈-lookup    : lookup i xs ∈ xs

  ∈-toList⁻   : v ∈ toList xs   → v ∈ xs
  ∈-fromList⁻ : v ∈ fromList xs → v ∈ xs
  ```

* Added new proof to `Data.Vec.Properties`:
  ```agda
  lookup-zipWith : lookup i (zipWith f xs ys) ≡ f (lookup i xs) (lookup i ys)
  ```
  Added laws for `updateAt`.
  Now laws for `_[_]≔_` are special instances of these.

* Added new proofs to `Data.Vec.Relation.Pointwise.Inductive`:
  ```agda
  tabulate⁺ : (∀ i → f i ~ g i) → Pointwise _~_ (tabulate f) (tabulate g)
  tabulate⁻ : Pointwise _~_ (tabulate f) (tabulate g) → (∀ i → f i ~ g i)
  ```

* Added new type to `Foreign.Haskell`:
  ```agda
  Pair : (A : Set ℓ) (B : Set ℓ′) : Set (ℓ ⊔ ℓ′)
  ```

* Added new function to `Function`:
>>>>>>> Vec-updateAt
  ```agda
  toℕ-cast    : toℕ (cast eq k) ≡ toℕ k
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

  _++_      : ∀ {l m} → All P l → All P m → All P (l List.++ m)
  _∷ʳ_      : ∀ {l : List A}{x} → All P l → P x → All P (l List.∷ʳ x)

  updateAt  : ∀ {x xs} → x ∈ xs → (P x → P x) → All P xs → All P xs
  _[_]%=_   : ∀ {x xs} → All P xs → x ∈ xs → (P x → P x) → All P xs
  _[_]≔_    : ∀ {x xs} → All P xs → x ∈ xs → P x → All P xs
  ```

* Added new operators to `Data.List.Base`:
  ```agda
  _[_]%=_ : (xs : List A) → Fin (length xs) → (A → A) → List A
  _[_]∷=_ : (xs : List A) → Fin (length xs) → A → List A
  _─_     : (xs : List A) → Fin (length xs) → List A
  ```

* Added new proofs to `Data.List.All.Properties`:
  ```agda
  respects : P Respects _≈_ → (All P) Respects _≋_
  ```

* Added new proof to `Data.List.Membership.Propositional.Properties`:
  ```agda
  ∈-allFin : (k : Fin n) → k ∈ allFin n
  ```

* Added new function to `Data.List.Membership.(Setoid/Propositional)`:
  ```agda
  _∷=_    : x ∈ xs → A → List A
  _─_     : (xs : List A) → x ∈ xs → List A
  ```

* Added new proofs to `Data.List.Membership.Setoid.Properties`:
  ```agda
  length-mapWith∈ : length (mapWith∈ xs f) ≡ length xs

  ∈-∷=⁺-updated   : v ∈ (x∈xs ∷= v)
  ∈-∷=⁺-untouched : x ≉ y → y ∈ xs → y ∈ (x∈xs ∷= v)
  ∈-∷=⁻           : y ≉ v → y ∈ (x∈xs ∷= v) → y ∈ xs

  map-∷=          : map f (x∈xs ∷= v) ≡ ∈-map⁺ f≈ pr ∷= f v
  ```

* Added new proofs to `Data.List.Properties`:
  ```agda
  length-%= : length (xs [ k ]%= f) ≡ length xs
  length-∷= : length (xs [ k ]∷= v) ≡ length xs
  map-∷=    : map f (xs [ k ]∷= v) ≡ map f xs [ cast eq k ]∷= f v
  length-─  : length (xs ─ k) ≡ pred (length xs)
  map-─     : map f (xs ─ k) ≡ map f xs ─ cast eq k
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

* Added new functions to `Data.Sum.Base`:
  ```agda
  fromDec : Dec P → P ⊎ ¬ P
  toDec   : P ⊎ ¬ P → Dec P
  ```

* Added new definitions to `Relation.Binary.PropositionalEquality`:
  - `_≡_↾¹_` equality of functions at a single point
  - `_≡_↾_` equality of functions at a subset of the domain

* Added new proofs to `Relation.Binary.PropositionalEquality`:

* Added new functions to `Data.Vec.Any.Properties`:
  ```agda
  lookup-index : (p : Any P xs) → P (lookup (index p) xs)
  fromList⁺    : List.Any P xs → Any P (fromList xs)
  fromList⁻    : Any P (fromList xs) → List.Any P xs
  toList⁺      : Any P xs → List.Any P (toList xs)
  toList⁻      : List.Any P (toList xs) → Any P xs
  ```

* Added new functions to `Data.Vec.Membership.Propositional.Properties`:
  ```agda
  fromAny : Any P xs → ∃ λ x → x ∈ xs × P x
  toAny   : x ∈ xs → P x → Any P xs
  ```

* Added new proofs to `Relation.Binary.Consequences`:
  ```agda
  wlog : Total _R_ → Symmetric Q → (∀ a b → a R b → Q a b) → ∀ a b → Q a b
  ```

* Added new proofs to `Relation.Binary.Lattice`:
  ```agda
  Lattice.setoid        : Setoid c ℓ
  BoundedLattice.setoid : Setoid c ℓ
  ```

* Added new operations and proofs to `Relation.Binary.Properties.HeytingAlgebra`:
  ```agda
  y≤x⇨y            : y ≤ x ⇨ y
  ⇨-unit           : x ⇨ x ≈ ⊤
  ⇨-drop           : (x ⇨ y) ∧ y ≈ y
  ⇨-app            : (x ⇨ y) ∧ x ≈ y ∧ x
  ⇨-relax          : _⇨_ Preserves₂ (flip _≤_) ⟶ _≤_ ⟶ _≤_
  ⇨-cong           : _⇨_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  ⇨-applyˡ         : w ≤ x → (x ⇨ y) ∧ w ≤ y
  ⇨-applyʳ         : w ≤ x → w ∧ (x ⇨ y) ≤ y
  ⇨-curry          : x ∧ y ⇨ z ≈ x ⇨ y ⇨ z
  ⇨ʳ-covariant     : (x ⇨_) Preserves _≤_ ⟶ _≤_
  ⇨ˡ-contravariant : (_⇨ x) Preserves (flip _≤_) ⟶ _≤_

  ¬_           : Op₁ Carrier
  x≤¬¬x        : x ≤ ¬ ¬ x
  de-morgan₁   : ¬ (x ∨ y) ≈ ¬ x ∧ ¬ y
  de-morgan₂-≤ : ¬ (x ∧ y) ≤ ¬ ¬ (¬ x ∨ ¬ y)
  de-morgan₂-≥ : ¬ ¬ (¬ x ∨ ¬ y) ≤ ¬ (x ∧ y)
  de-morgan₂   : ¬ (x ∧ y) ≈ ¬ ¬ (¬ x ∨ ¬ y)
  weak-lem     : ¬ ¬ (¬ x ∨ x) ≈ ⊤
  ```

* Added new proofs to `Relation.Binary.Properties.JoinLattice`:
  ```agda
  x≤y⇒x∨y≈y : x ≤ y → x ∨ y ≈ y
  ```

* Added new proofs to `Relation.Binary.Properties.Lattice`:
  ```agda
  ∧≤∨            : x ∧ y ≤ x ∨ y
  quadrilateral₁ : x ∨ y ≈ x → x ∧ y ≈ y
  quadrilateral₂ : x ∧ y ≈ y → x ∨ y ≈ x
  collapse₁      : x ≈ y → x ∧ y ≈ x ∨ y
  collapse₂      : x ∨ y ≤ x ∧ y → x ≈ y
  ```

* Added new proofs to `Relation.Binary.Properties.MeetLattice`:
  ```agda
  y≤x⇒x∧y≈y : y ≤ x → x ∧ y ≈ y
  ```
