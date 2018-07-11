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


#### Overhaul of `Data.Container`, `Data.W` and `Codata.(Musical.)M`

* Made `Data.Container` (and associated modules) more level-polymorphic

* Created `Data.Container.Core` for the core definition of `Container`,
  container morphism, All, and Any. This breaks the dependency cycle
  with `Data.W` and `Codata.Musical.M`.

* Refactored `Data.W` and `Codata.Musical.M` to use `Container`.

* Added new functions to `Codata.Musical.M`:
  ```agda
  map    : (C₁ ⇒ C₂) → M C₁ → M C₂
  unfold : (S → ⟦ C ⟧ S) → S → M C
  ```

* Added new module `Codata.M` using sized types and copatterns containing:
  ```agda
  M      : Container s p → Size → Set (s ⊔ p)
  head   : M C i → Shape
  tail   : (x : M C ∞) → Position (head x) → M C ∞
  map    : (C₁ ⇒ C₂) → M C₁ i → M C₂ i
  unfold : (S → ⟦ C ⟧ S) → S → M C i
  ```


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
  singleton⁺ : P x → Any P [ x ]
  singleton⁻ : Any P [ x ] → P x
  ++-insert  : P x → Any P (xs ++ [ x ] ++ ys)
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

* Added new result to `Function.Relation.TypeIsomorphisms`:
  ```agda
  ×-comm : (A × B) ↔ (B × A)
  ```

* Added the following types in `Relation.Unary`:
  ```agda
  Satisfiable P = ∃ λ x → x ∈ P
  ```
