Version TODO
============

The library has been tested using Agda version TODO.

Important changes since 0.16:

Non-backwards compatible changes
--------------------------------

#### New codata library

* A new `Codata` library using copatterns and sized types rather
  than musical notation has been added. The library is built around a generic
  notion of coinductive `Thunk` and provides the basic data types:
  ```agda
  Codata.Thunk
  Codata.Colist
  Codata.Conat
  Codata.Covec
  Codata.Delay
  Codata.Stream
  ```
  Each coinductive type comes with a notion of bisimilarity in the corresponding
  `Codata.X.Bisimilarity` module and at least a couple of proofs demonstrating
  how they can be used in `Codata.X.Properties`. This library is somewhat
  experimental and may undergo minor changes in later versions.

* To avoid confusion, the old codata modules that previously lived in the `Data`
  directory have been moved to the folder `Codata.Musical`
  ```agda
  Data.Cofin  ↦ Codata.Musical.Cofin
  Data.Colist ↦ Codata.Musical.Colist
  Data.Conat  ↦ Codata.Musical.Conat
  Data.Covec  ↦ Codata.Musical.Covec
  Data.M      ↦ Codata.Musical.M
  Data.Stream ↦ Codata.Musical.Stream
  ```

* Each new-style coinduction type comes with a `fromMusical` function converting
  old-style coinduction values to new-style ones.

* The type `Costring` and method `toCostring` have been moved from `Data.String`
  to a new module `Codata.Musical.Costring`.

#### Improved consistency between `Data.(List/Vec).(Any/All/Membership)`

* Added new module `Data.Vec.Any`.

* The type `_∈_` has been moved from `Data.Vec` to the new module
  `Data.Vec.Membership.Propositional` and has been reimplemented using
  `Any` from `Data.Vec.Any`. In particular this means that you must now
  pass a `refl` proof to the `here` constructor.

* The proofs associated with `_∈_` have been moved from `Data.Vec.Properties`
  to the new module  `Data.Vec.Membership.Propositional.Properties`
  and have been renamed as follows:
  ```agda
  ∈-++ₗ      ↦ ∈-++⁺ˡ
  ∈-++ᵣ      ↦ ∈-++⁺ʳ
  ∈-map      ↦ ∈-map⁺
  ∈-tabulate ↦ ∈-tabulate⁺
  ∈-allFin   ↦ ∈-allFin⁺
  ∈-allPairs ↦ ∈-allPairs⁺
  ∈⇒List-∈   ↦ ∈-toList⁺
  List-∈⇒∈   ↦ ∈-fromList⁺
  ```

* The proofs `All-universal` and `All-irrelevance` have been moved from
  `Data.(List/Vec).All.Properties` and renamed `universal` and `irrelevant` in
  `Data.(List/Vec).All`.

* The existing function `tabulate` in `Data.Vec.All` has been renamed
  `universal`. The name `tabulate` now refers to a function with following type:
  ```agda
  tabulate : (∀ i → P (Vec.lookup i xs)) → All P {k} xs
  ```

#### Deprecating `Data.Fin.Dec`:

* This module has been deprecated as it's non-standard position
  is causing dependency cycles. The move also makes finding
  subset properties easier.

* The following have been moved to `Data.Fin.Properties`:
  `decFinSubset`, `any?`, `all?`, `¬∀⟶∃¬-smallest`, `¬∀⟶∃¬`.

* The following proofs have been moved to `Data.Fin.Subset.Properties`:
  `_∈?_`, `_⊆?_`, `nonempty?`, `anySubset?` and `decLift`. The latter
  has been renamed to `Lift?`.

* The file `Data.Fin.Dec` still exists for backwards compatibility
  and exports all the old names, but may be removed in some
  future version.

### Overhaul of `Data.X.Categorical`

* Created `Codata.Delay.Categorical`:
  ```agda
  functor                : RawFunctor (λ A → Delay A i)
  Sequential.applicative : RawApplicative (λ A → Delay A i)
  Sequential.monad       : RawMonad (λ A → Delay A i)
  Sequential.monadZero   : RawMonadZero (λ A → Delay A i)
  Zippy.applicative      : RawApplicative (λ A → Delay A i)
  ```

* Created `Codata.Stream.Categorical`:
  ```agda
  functor     : RawFunctor (λ A → Stream A i)
  applicative : RawApplicative (λ A → Stream A i)
  ```

* In `Data.List.Categorical` renamed and added functions:
  ```agda
  functor     : RawFunctor List
  applicative : RawApplicative List
  monadT      : RawMonad M → RawMonad (M ∘′ List)
  sequenceA   : RawApplicative F → List (F A) → F (List A)
  mapA        : RawApplicative F → (A → F B) → List A → F (List B)
  forA        : RawApplicative F → List A → (A → F B) → F (List B)
  sequence    ↦ sequenceM
  forM        : RawMonad M → List A → (A → M B) → M (List B)
  ```

* Created `Data.List.NonEmpty.Categorical`, moved `monad` into it
  from `Data.List.NonEmpty` and added new functions:
  ```agda
  functor     : RawFunctor List⁺
  applicative : RawApplicative List⁺
  monadT      : RawMonad M → RawMonad (M ∘′ List⁺)
  sequenceA   : RawApplicative F → List⁺ (F A) → F (List⁺ A)
  mapA        : RawApplicative F → (A → F B) → List⁺ A → F (List⁺ B)
  forA        : RawApplicative F → List⁺ A → (A → F B) → F (List⁺ B)
  sequenceM   : RawMonad M → List⁺ (M A) → M (List⁺ A)
  mapM        : RawMonad M → (A → M B) → List⁺ A → M (List⁺ B)
  forM        : RawMonad M → List⁺ A → (A → M B) → M (List⁺ B)
  ```

* Created `Data.Maybe.Categorical`, moved `functor`, `monadT`, `monad`,
  `monadZero` and `monadPlus` into it from `Data.Maybe` and added the
  following functions:
  ```agda
  sequenceA : RawApplicative F → Maybe (F A) → F (Maybe A)
  mapA      : RawApplicative F → (A → F B) → Maybe A → F (Maybe B)
  forA      : RawApplicative F → Maybe A → (A → F B) → F (Maybe B)
  sequenceM : RawMonad M → Maybe (M A) → M (Maybe A)
  mapM      : RawMonad M → (A → M B) → Maybe A → M (Maybe B)
  forM      : RawMonad M → Maybe A → (A → M B) → M (Maybe B)
  ```

* Created `Data.Product.N-ary.Categorical` and added:
  ```agda
  functor     : RawFunctor (_^ n)
  applicative : RawApplicative (_^ n)
  sequenceA : RawApplicative F → Vec (F A) n → F (A ^ n)
  mapA      : RawApplicative F → (A → F B) → A ^ n → F (B ^ n)
  forA      : RawApplicative F → A ^ n → (A → F B) → F (B ^ n)
  sequenceM : RawMonad M → Vec (M A) n → M (A ^ n)
  mapM      : RawMonad M → (A → M B) → A ^ n → M (B ^ n)
  forM      : RawMonad M → A ^ n → (A → M B) → M (B ^ n)

* Added new functions to `Data.Vec.Categorical`:
  ```
  sequenceA : RawApplicative F → Vec (F A) n → F (Vec A n)
  mapA      : RawApplicative F → (A → F B) → Vec A n → F (Vec B n)
  forA      : RawApplicative F → Vec A n → (A → F B) → F (Vec B n)
  sequenceM : RawMonad M → Vec (M A) n → M (Vec A n)
  mapM      : RawMonad M → (A → M B) → Vec A n → M (Vec B n)
  forM      : RawMonad M → Vec A n → (A → M B) → M (Vec B n)
  ```

#### Other

* The `Data.List.Relation.Sublist` directory has been moved to
  `Data.List.Relation.Sublist.Extensional` to make room for the
  new `Data.List.Relation.Sublist.Inductive` hierarchy.

* The types `IrrelevantPred` and `IrrelevantRel` in
  `Relation.Binary.PropositionalEquality` have both been renamed to
  `Irrelevant` and have been moved to `Relation.Unary` and
  `Relation.Binary` respectively.

* Made the `Set` argument implicit in `Data.Maybe.Base`'s `From-just`
  to be consistent with the definition of `Data.Sum`'s `From-injₙ`.

* Renamed `Data.Product`'s `,_` to `-,_` to avoid conflict with the right
  section of `_,_`.

* Made the target level of `Level`'s `Lift` explicit.

* Made `Data.Container` (and associated modules) more level-polymorphic and
  moved the core definitions to `Data.Container.Core`.

* Changed the precedence level of `_$_` (and variants) to `-1`. This makes
  it interact well with `_∋_` in e.g. `f $ Maybe A ∋ do (...)`.

Other major changes
-------------------

* Added new module `Algebra.Properties.CommutativeMonoid`. This contains proofs
  of lots of properties of summation, including 'big summation'.

* Added new modules `Data.List.Relation.Permutation.Inductive(.Properties)`,
  which give an inductive definition of permutations over lists.

* Added a very barebones new module `Data.These` for the classic either-or-both
  Haskell datatype.

* Added new module `Data.List.Relation.Sublist.Inductive` which gives
  an inductive definition of the sublist relation (i.e. order-preserving embeddings).

* Added new module `Data.Sum.Categorical`:
  ```agda
  Sumₗ.functor     : RawFunctor (A ⊎_)
  Sumₗ.applicative : RawApplicative (A ⊎_)
  Sumₗ.monadT      : RawMonad M → RawMonad (M ∘′ (A ⊎_))
  Sumₗ.monad       : RawMonad (A ⊎_)
  Sumₗ.sequenceA   : RawApplicative F → Sumₗ (F A) → F (Sumₗ A)
  Sumₗ.mapA        : RawApplicative F → (A → F B) → Sumₗ A → F (Sumₗ B)
  Sumₗ.forA        : RawApplicative F → Sumₗ A → (A → F B) → F (Sumₗ B)
  Sumₗ.sequenceM   : RawMonad M → Sumₗ (M A) → M (Sumₗ A)
  Sumₗ.mapM        : RawMonad M → (A → M B) → Sumₗ A → M (Sumₗ B)
  Sumₗ.forM        : RawMonad M → Sumₗ A → (A → M B) → M (Sumₗ B)
  Sumᵣ.functor     : RawFunctor (_⊎ B)
  Sumᵣ.applicative : RawApplicative (_⊎ B)
  Sumᵣ.monadT      : RawMonad M → RawMonad (M ∘′ (_⊎ B))
  Sumᵣ.monad       : RawMonad (_⊎ B)
  Sumᵣ.sequenceA   : RawApplicative F → Sumᵣ (F A) → F (Sumᵣ A)
  Sumᵣ.mapA        : RawApplicative F → (A → F B) → Sumᵣ A → F (Sumᵣ B)
  Sumᵣ.forA        : RawApplicative F → Sumᵣ A → (A → F B) → F (Sumᵣ B)
  Sumᵣ.sequenceM   : RawMonad M → Sumᵣ (M A) → M (Sumᵣ A)
  Sumᵣ.mapM        : RawMonad M → (A → M B) → Sumᵣ A → M (Sumᵣ B)
  Sumᵣ.forM        : RawMonad M → Sumᵣ A → (A → M B) → M (Sumᵣ B)
  ```

* Added new module `Data.Product.Categorical`:
  ```agda
  Productₗ.functor     : (A : RawMonoid a e) → RawFunctor (A ×_)
  Productₗ.applicative : (A : RawMonoid a e) → RawApplicative (A ×_)
  Productₗ.monadT      : (A : RawMonoid a e) → RawMonad M → RawMonad (M ∘′ (A ×_))
  Productₗ.monad       : (A : RawMonoid a e) → RawMonad (A ×_)
  Productₗ.sequenceA   : RawApplicative F → Productₗ (F A) → F (Productₗ A)
  Productₗ.mapA        : RawApplicative F → (A → F B) → Productₗ A → F (Productₗ B)
  Productₗ.forA        : RawApplicative F → Productₗ A → (A → F B) → F (Productₗ B)
  Productₗ.sequenceM   : RawMonad M → Productₗ (M A) → M (Productₗ A)
  Productₗ.mapM        : RawMonad M → (A → M B) → Productₗ A → M (Productₗ B)
  Productₗ.forM        : RawMonad M → Productₗ A → (A → M B) → M (Productₗ B)
  Productᵣ.functor     : (B : RawMonoid b e) → RawFunctor (_× B)
  Productᵣ.applicative : (B : RawMonoid b e) → RawApplicative (_× B)
  Productᵣ.monadT      : (B : RawMonoid b e) → RawMonad M → RawMonad (M ∘′ (_× B))
  Productᵣ.monad       : (B : RawMonoid b e) → RawMonad (_× B)
  Productᵣ.sequenceA   : RawApplicative F → Productᵣ (F A) → F (Productᵣ A)
  Productᵣ.mapA        : RawApplicative F → (A → F B) → Productᵣ A → F (Productᵣ B)
  Productᵣ.forA        : RawApplicative F → Productᵣ A → (A → F B) → F (Productᵣ B)
  Productᵣ.sequenceM   : RawMonad M → Productᵣ (M A) → M (Productᵣ A)
  Productᵣ.mapM        : RawMonad M → (A → M B) → Productᵣ A → M (Productᵣ B)
  Productᵣ.forM        : RawMonad M → Productᵣ A → (A → M B) → M (Productᵣ B)
  ```

Deprecated features
-------------------

The following deprecations have occurred as part of a drive to improve consistency across
the library. The deprecated names still exist and therefore all existing code should still
work, however they have been deprecated and use of any new names is encouraged. Although not
anticipated any time soon, they may eventually be removed in some future release of the library.

* In `Data.Nat.Divisibility`:
  ```
  nonZeroDivisor-lemma
  ```

Other minor additions
---------------------

* Added new functions to `Codata.Delay`:
  ```agda
  alignWith : (These A B → C) → Delay A i → Delay B i → Delay C i
  zip       : Delay A i → Delay B i → Delay (A × B) i
  align     : Delay A i → Delay B i → Delay (These A B) i
  ```

* Added new proof to `Data.Fin.Permutation`:
  ```agda
  refute : m ≢ n → ¬ Permutation m n
  ```
  Additionally the definitions `punchIn-permute` and `punchIn-permute′`
  have been generalised to work with heterogeneous permutations.

* Added new proof to `Data.Fin.Properties`:
  ```agda
  toℕ-fromℕ≤″ : toℕ (fromℕ≤″ m m<n) ≡ m
  ```

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

* Added new proofs to `Data.List.Membership.(Setoid/Propositional).Properties`:
  ```agda
  ∈-insert : v ≈ v′ → v ∈ xs ++ [ v′ ] ++ ys
  ∈-∃++    : v ∈ xs → ∃₂ λ ys zs → ∃ λ w → v ≈ w × xs ≋ ys ++ [ w ] ++ zs
  ```

* Added new function to `Data.List.NonEmpty`:
  ```agda
  concatMap : (A → List⁺ B) → List⁺ A → List⁺ B
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

* Added new functions to `Data.Nat.Properties`:
  ```agda
  *-distribˡ-∸ : _*_ DistributesOverˡ _∸_
  *-distrib-∸  : _*_ DistributesOver _∸_
  ^-*-assoc    : (m ^ n) ^ p ≡ m ^ (n * p)
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

* Added new proofs to `Data.Vec.Properties.All`:
  ```agda
  toList⁺   : All P (toList xs) → All P xs
  toList⁻   : All P xs → All P (toList xs)

  fromList⁺ : All P xs → All P (fromList xs)
  fromList⁻ : All P (fromList xs) → All P xs
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
  ```agda
  typeOf : {A : Set a} → A → Set a
  ```

* Added new result to `Function.Relation.TypeIsomorphisms`:
  ```agda
  ×-comm : (A × B) ↔ (B × A)
  ```

* Added new type and function to `Function.Bijection`:
  ```agda
  From ⤖ To = Bijection (P.setoid From) (P.setoid To)

  bijection : (∀ {x y} → to x ≡ to y → x ≡ y) → (∀ x → to (from x) ≡ x) → From ⤖ To
  ```

* Added new function to `Function.Injection`:
  ```agda
  injection : (∀ {x y} → to x ≡ to y → x ≡ y) → From ↣ To
  ```

* Added new function to `Function.Inverse`:
  ```agda
  inverse : (∀ x → from (to x) ≡ x) → (∀ x → to (from x) ≡ x) → From ↔ To
  ```

* Added new function to `Function.LeftInverse`:
  ```agda
  leftInverse : (∀ x → from (to x) ≡ x) → From ↞ To
  ```

* Added new proofs to `Function.Related.TypeIsomorphisms`:
  ```agda
  ×-≡×≡↔≡,≡ : (x ≡ proj₁ p × y ≡ proj₂ p) ↔ (x , y) ≡ p
  ×-comm    : (A × B) ↔ (B × A)
  ```

* Added new function to `Function.Surjection`:
  ```agda
  surjection : (∀ x → to (from x) ≡ x) → From ↠ To
  ```

* Added new functions to `Level`:
  ```agda
  _ℕ+_ : Nat → Level → Level
  #_   : Nat → Level
  ```

* Added the following types in `Relation.Unary`:
  ```agda
  Satisfiable P = ∃ λ x → x ∈ P
  ```

* Added the following proofs in `Relation.Unary.Properties`:
  ```agda
  ∅? : Decidable ∅
  U? : Decidable U
  ```
