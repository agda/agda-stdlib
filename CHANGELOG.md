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

### Overhaul of `Data.X.Categorical`

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

* Added new module `Data.List.Relation.Sublist.Inductive` which gives
  an inductive definition of the sublist relation (i.e. order-preserving embeddings).

* Added new modules `Data.List.Relation.Permutation.Inductive(.Properties)`,
  which give an inductive definition of permutations over lists.

* Added new module `Algebra.Properties.CommutativeMonoid`. This contains proofs
  of lots of properties of summation, including 'big summation'.

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
  uncons : List A → Maybe (A × List A)
  head   : List A → Maybe A
  tail   : List A → Maybe (List A)
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

* Added new function to `Data.Maybe.Base`:
  ```agda
  fromMaybe : A → Maybe A → A
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

* Added new type to `Foreign.Haskell`:
  ```agda
  Pair : (A : Set ℓ) (B : Set ℓ′) : Set (ℓ ⊔ ℓ′)
  ```

* Added new function to `Function`:
  ```agda
  typeOf : {A : Set a} → A → Set a
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

* Added new proof to `Function.Related.TypeIsomorphisms`:
  ```agda
  ×-≡×≡↔≡,≡ : (x ≡ proj₁ p × y ≡ proj₂ p) ↔ (x , y) ≡ p
  ×-comm    : (A × B) ↔ (B × A)
  ```

* Added new function to `Function.Surjection`:
  ```agda
  surjection : (∀ x → to (from x) ≡ x) → From ↠ To
  ```

* Added the following types in `Relation.Unary`:
  ```agda
  Satisfiable P = ∃ λ x → x ∈ P
  ```
