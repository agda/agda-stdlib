Version 2.2
===========

The library has been tested using Agda 2.7.0 and 2.7.0.1.

Highlights
----------

* Added missing morphisms between the more advanced algebraic structures.

* Added many missing lemmas about positive and negative rational numbers.

Bug-fixes
---------

* Made the types for `≡-syntax` in `Relation.Binary.HeterogeneousEquality` more general.
  These operators are used for equational reasoning of heterogeneous equality
  `x ≅ y`, but previously the three operators in `≡-syntax` unnecessarily required
  `x` and `y` to have the same type, making them unusable in many situations.

* Removed unnecessary parameter `#-trans : Transitive _#_` from
  `Relation.Binary.Reasoning.Base.Apartness`.

* The `IsSemiringWithoutOne` record no longer incorrectly exposes the `Carrier` field
  inherited from `Setoid` when opening the record publicly.

Non-backwards compatible changes
--------------------------------

* In `Data.List.Relation.Binary.Sublist.Propositional.Properties` the implicit module parameters `a` and `A` have been replaced with `variable`s. This should be a backwards compatible change for the majority of uses, and would only be non-backwards compatible if for some reason you were explicitly supplying these implicit parameters when importing the module. Explicitly supplying the implicit parameters for functions exported from the module should not be affected.

* [issue #2504](https://github.com/agda/agda-stdlib/issues/2504) and [issue #2519](https://github.com/agda/agda-stdlib/issues/2510) In `Data.Nat.Base` the definitions of `_≤′_` and `_≤‴_` have been modified to make the witness to equality explicit in new constructors `≤′-reflexive` and `≤‴-reflexive`; pattern synonyms `≤′-refl` and `≤‴-refl` have been added for backwards compatibility. This should be a backwards compatible change for the majority of uses, but the change in parametrisation means that these patterns are *not* necessarily well-formed if the old implicit arguments `m`,`n` are supplied explicitly.

Minor improvements
------------------

* In `Function.Related.TypeIsomorphisms`, the unprimed versions are more level polymorphic; and the primed versions retain `Level` homogeneous types for the `Semiring` axioms to hold.

Deprecated modules
------------------

Deprecated names
----------------

* In `Algebra.Properties.CommutativeMagma.Divisibility`:
  ```agda
  ∣-factors    ↦  x|xy∧y|xy
  ∣-factors-≈  ↦  xy≈z⇒x|z∧y|z
  ```

* In `Algebra.Properties.Magma.Divisibility`:
  ```agda
  ∣-respˡ   ↦  ∣-respˡ-≈
  ∣-respʳ   ↦  ∣-respʳ-≈
  ∣-resp    ↦  ∣-resp-≈
 ```

* In `Algebra.Solver.CommutativeMonoid`:
  ```agda
  normalise-correct  ↦  Algebra.Solver.CommutativeMonoid.Normal.correct
  sg                 ↦  Algebra.Solver.CommutativeMonoid.Normal.singleton
  sg-correct         ↦  Algebra.Solver.CommutativeMonoid.Normal.singleton-correct
  ```

* In `Algebra.Solver.IdempotentCommutativeMonoid`:
  ```agda
  flip12             ↦  Algebra.Properties.CommutativeSemigroup.xy∙z≈y∙xz
  distr              ↦  Algebra.Properties.IdempotentCommutativeMonoid.∙-distrˡ-∙
  normalise-correct  ↦  Algebra.Solver.IdempotentCommutativeMonoid.Normal.correct
  sg                 ↦  Algebra.Solver.IdempotentCommutativeMonoid.Normal.singleton
  sg-correct         ↦  Algebra.Solver.IdempotentCommutativeMonoid.Normal.singleton-correct
  ```

* In `Algebra.Solver.Monoid`:
  ```agda
  homomorphic        ↦  Algebra.Solver.Monoid.Normal.comp-correct
  normalise-correct  ↦  Algebra.Solver.Monoid.Normal.correct
  ```

* In `Data.List.Properties`:
  ```agda
  concat-[-]   ↦  concat-map-[_]
  ```

* In `Data.List.Relation.Binary.Permutation.Setoid.Properties`:
  ```agda
  split  ↦  ↭-split
  ```

* In `Data.List.Relation.Unary.All.Properties`:
  ```agda
  takeWhile⁻  ↦  all-takeWhile
  ```

* In `Data.Vec.Properties`:
  ```agda
  ++-assoc _      ↦  ++-assoc-eqFree
  ++-identityʳ _  ↦  ++-identityʳ-eqFree
  unfold-∷ʳ _     ↦  unfold-∷ʳ-eqFree
  ++-∷ʳ _         ↦  ++-∷ʳ-eqFree
  ∷ʳ-++ _         ↦  ∷ʳ-++-eqFree
  reverse-++ _    ↦  reverse-++-eqFree
  ∷-ʳ++ _         ↦  ∷-ʳ++-eqFree
  ++-ʳ++ _        ↦  ++-ʳ++-eqFree
  ʳ++-ʳ++ _       ↦  ʳ++-ʳ++-eqFree
  ```

New modules
-----------

* Consequences of module monomorphisms
  ```
  Algebra.Module.Morphism.BimoduleMonomorphism
  Algebra.Module.Morphism.BisemimoduleMonomorphism
  Algebra.Module.Morphism.LeftModuleMonomorphism
  Algebra.Module.Morphism.LeftSemimoduleMonomorphism
  Algebra.Module.Morphism.ModuleMonomorphism
  Algebra.Module.Morphism.RightModuleMonomorphism
  Algebra.Module.Morphism.RightSemimoduleMonomorphism
  Algebra.Module.Morphism.SemimoduleMonomorphism
  ```

* Bundled morphisms between (raw) algebraic structures:
  ```
  Algebra.Morphism.Bundles
  ```

* Properties of `IdempotentCommutativeMonoid`s refactored out from `Algebra.Solver.IdempotentCommutativeMonoid`:
  ```
  Algebra.Properties.IdempotentCommutativeMonoid
  ```

* Refactoring of the `Algebra.Solver.*Monoid` implementations, via
  a single `Solver` module API based on the existing `Expr`, and
  a common `Normal`-form API:
  ```
  Algebra.Solver.CommutativeMonoid.Normal
  Algebra.Solver.IdempotentCommutativeMonoid.Normal
  Algebra.Solver.Monoid.Expression
  Algebra.Solver.Monoid.Normal
  Algebra.Solver.Monoid.Solver
  ```
  NB Imports of the existing proof procedures `solve` and `prove` etc. should still be via the top-level interfaces in `Algebra.Solver.*Monoid`.

* `Data.List.Relation.Binary.Disjoint.Propositional.Properties`:
  Propositional counterpart to `Data.List.Relation.Binary.Disjoint.Setoid.Properties`

* Properties of list permutations that require the `--with-K` flag:
  ```
  Data.List.Relation.Binary.Permutation.Propositional.Properties.WithK
  ```

* Refactored `Data.Refinement` into:
  ```agda
  Data.Refinement.Base
  Data.Refinement.Properties
  ```

* Added implementation of Haskell-like `Foldable`:
  ```agda
  Effect.Foldable
  Data.List.Effectful.Foldable
  Data.Vec.Effectful.Foldable
  ```

* Raw bundles for the `Relation.Binary.Bundles` hierarchy:
  ```agda
  Relation.Binary.Bundles.Raw
  ```

Additions to existing modules
-----------------------------

* In `Algebra.Bundles.KleeneAlgebra`:
  ```agda
  rawKleeneAlgebra : RawKleeneAlgebra _ _
  ```

* In `Algebra.Bundles.Raw.*`
  ```agda
  rawSetoid : RawSetoid c ℓ
  ```

* In `Algebra.Bundles.Raw.RawRingWithoutOne`
  ```agda
  rawNearSemiring : RawNearSemiring c ℓ
  ```

* Exporting more `Raw` substructures from `Algebra.Bundles.Ring`:
  ```agda
  rawNearSemiring   : RawNearSemiring _ _
  rawRingWithoutOne : RawRingWithoutOne _ _
  +-rawGroup        : RawGroup _ _
  ```

* Exporting `RawRingWithoutOne` and `(Raw)NearSemiring` subbundles from
  `Algebra.Bundles.RingWithoutOne`:
  ```agda
  nearSemiring      : NearSemiring _ _
  rawNearSemiring   : RawNearSemiring _ _
  rawRingWithoutOne : RawRingWithoutOne _ _
  ```

* In `Algebra.Morphism.Construct.Composition`:
  ```agda
  magmaHomomorphism          : MagmaHomomorphism M₁.rawMagma M₂.rawMagma →
                               MagmaHomomorphism M₂.rawMagma M₃.rawMagma →
                               MagmaHomomorphism M₁.rawMagma M₃.rawMagma
  monoidHomomorphism         : MonoidHomomorphism M₁.rawMonoid M₂.rawMonoid →
                               MonoidHomomorphism M₂.rawMonoid M₃.rawMonoid →
                               MonoidHomomorphism M₁.rawMonoid M₃.rawMonoid
  groupHomomorphism          : GroupHomomorphism M₁.rawGroup M₂.rawGroup →
                               GroupHomomorphism M₂.rawGroup M₃.rawGroup →
                               GroupHomomorphism M₁.rawGroup M₃.rawGroup
  nearSemiringHomomorphism   : NearSemiringHomomorphism M₁.rawNearSemiring M₂.rawNearSemiring →
                               NearSemiringHomomorphism M₂.rawNearSemiring M₃.rawNearSemiring →
                               NearSemiringHomomorphism M₁.rawNearSemiring M₃.rawNearSemiring
  semiringHomomorphism       : SemiringHomomorphism M₁.rawSemiring M₂.rawSemiring →
                               SemiringHomomorphism M₂.rawSemiring M₃.rawSemiring →
                               SemiringHomomorphism M₁.rawSemiring M₃.rawSemiring
  kleeneAlgebraHomomorphism  : KleeneAlgebraHomomorphism M₁.rawKleeneAlgebra M₂.rawKleeneAlgebra →
                               KleeneAlgebraHomomorphism M₂.rawKleeneAlgebra M₃.rawKleeneAlgebra →
                               KleeneAlgebraHomomorphism M₁.rawKleeneAlgebra M₃.rawKleeneAlgebra
  nearSemiringHomomorphism   : NearSemiringHomomorphism M₁.rawNearSemiring M₂.rawNearSemiring →
                               NearSemiringHomomorphism M₂.rawNearSemiring M₃.rawNearSemiring →
                               NearSemiringHomomorphism M₁.rawNearSemiring M₃.rawNearSemiring
  ringWithoutOneHomomorphism : RingWithoutOneHomomorphism M₁.rawRingWithoutOne M₂.rawRingWithoutOne →
                               RingWithoutOneHomomorphism M₂.rawRingWithoutOne M₃.rawRingWithoutOne →
                               RingWithoutOneHomomorphism M₁.rawRingWithoutOne M₃.rawRingWithoutOne
  ringHomomorphism           : RingHomomorphism M₁.rawRing M₂.rawRing →
                               RingHomomorphism M₂.rawRing M₃.rawRing →
                               RingHomomorphism M₁.rawRing M₃.rawRing
  quasigroupHomomorphism     : QuasigroupHomomorphism M₁.rawQuasigroup M₂.rawQuasigroup →
                               QuasigroupHomomorphism M₂.rawQuasigroup M₃.rawQuasigroup →
                               QuasigroupHomomorphism M₁.rawQuasigroup M₃.rawQuasigroup
  loopHomomorphism           : LoopHomomorphism M₁.rawLoop M₂.rawLoop →
                               LoopHomomorphism M₂.rawLoop M₃.rawLoop →
                               LoopHomomorphism M₁.rawLoop M₃.rawLoop
  ```

* In `Algebra.Morphism.Construct.Identity`:
  ```agda
  magmaHomomorphism          : MagmaHomomorphism M.rawMagma M.rawMagma
  monoidHomomorphism         : MonoidHomomorphism M.rawMonoid M.rawMonoid
  groupHomomorphism          : GroupHomomorphism M.rawGroup M.rawGroup
  nearSemiringHomomorphism   : NearSemiringHomomorphism M.raw M.raw
  semiringHomomorphism       : SemiringHomomorphism M.rawNearSemiring M.rawNearSemiring
  kleeneAlgebraHomomorphism  : KleeneAlgebraHomomorphism M.rawKleeneAlgebra M.rawKleeneAlgebra
  nearSemiringHomomorphism   : NearSemiringHomomorphism M.rawNearSemiring M.rawNearSemiring
  ringWithoutOneHomomorphism : RingWithoutOneHomomorphism M.rawRingWithoutOne M.rawRingWithoutOne
  ringHomomorphism           : RingHomomorphism M.rawRing M.rawRing
  quasigroupHomomorphism     : QuasigroupHomomorphism M.rawQuasigroup M.rawQuasigroup
  loopHomomorphism           : LoopHomomorphism M.rawLoop M.rawLoop
  ```

* In `Algebra.Morphism.Structures.RingMorphisms`
  ```agda
  isRingWithoutOneHomomorphism : IsRingWithoutOneHomomorphism ⟦_⟧
  ```

* In `Algebra.Morphism.Structures.RingWithoutOneMorphisms`
  ```agda
  isNearSemiringHomomorphism : IsNearSemiringHomomorphism ⟦_⟧
  ```

* In `Algebra.Structures.IsSemiringWithoutOne`:
  ```agda
  distribˡ : * DistributesOverˡ +
  distribʳ : * DistributesOverʳ +
  +-cong : Congruent +
  +-congˡ : LeftCongruent +
  +-congʳ : RightCongruent +
  +-assoc : Associative +
  +-identity : Identity 0# +
  +-identityˡ : LeftIdentity 0# +
  +-identityʳ : RightIdentity 0# +
  ```

* Properties of non-divisibility in `Algebra.Properties.Magma.Divisibility`:
  ```agda
  ∤-respˡ-≈ : _∤_ Respectsˡ _≈_
  ∤-respʳ-≈ : _∤_ Respectsʳ _≈_
  ∤-resp-≈  : _∤_ Respects₂ _≈_
  ∤∤-sym    : Symmetric _∤∤_
  ∤∤-respˡ-≈ : _∤∤_ Respectsˡ _≈_
  ∤∤-respʳ-≈ : _∤∤_ Respectsʳ _≈_
  ∤∤-resp-≈  : _∤∤_ Respects₂ _≈_
  ```

* In `Algebra.Solver.Ring`
  ```agda
  Env : ℕ → Set _
  Env = Vec Carrier
 ```

* In `Algebra.Structures.RingWithoutOne`:
  ```agda
  isNearSemiring      : IsNearSemiring _ _
 ```

* In `Data.List.Membership.Propositional.Properties`:
  ```agda
  ∈-AllPairs₂    : AllPairs R xs → x ∈ xs → y ∈ xs → x ≡ y ⊎ R x y ⊎ R y x
  ∈-map∘filter⁻  : y ∈ map f (filter P? xs) → (∃[ x ] x ∈ xs × y ≡ f x × P x)
  ∈-map∘filter⁺  : (∃[ x ] x ∈ xs × y ≡ f x × P x) → y ∈ map f (filter P? xs)
  ∈-concatMap⁺   : Any ((y ∈_) ∘ f) xs → y ∈ concatMap f xs
  ∈-concatMap⁻   : y ∈ concatMap f xs → Any ((y ∈_) ∘ f) xs
  ++-∈⇔          : v ∈ xs ++ ys ⇔ (v ∈ xs ⊎ v ∈ ys)
  []∉map∷        : [] ∉ map (x ∷_) xss
  map∷⁻          : xs ∈ map (y ∷_) xss → ∃[ ys ] ys ∈ xss × xs ≡ y ∷ ys
  map∷-decomp∈   : (x ∷ xs) ∈ map (y ∷_) xss → x ≡ y × xs ∈ xss
  ∈-map∷⁻        : xs ∈ map (x ∷_) xss → x ∈ xs
  ∉[]            : x ∉ []
  deduplicate-∈⇔ : z ∈ xs ⇔ z ∈ deduplicate _≈?_ xs
  ```

* In `Data.List.Membership.Propositional.Properties.WithK`:
  ```agda
  unique∧set⇒bag : Unique xs → Unique ys → xs ∼[ set ] ys → xs ∼[ bag ] ys
  ```

* In `Data.List.Membership.Setoid.Properties`:
  ```agda
  ∉⇒All[≉]       : x ∉ xs → All (x ≉_) xs
  All[≉]⇒∉       : All (x ≉_) xs → x ∉ xs
  Any-∈-swap     : Any (_∈ ys) xs → Any (_∈ xs) ys
  All-∉-swap     : All (_∉ ys) xs → All (_∉ xs) ys
  ∈-map∘filter⁻  : y ∈₂ map f (filter P? xs) → ∃[ x ] x ∈₁ xs × y ≈₂ f x × P x
  ∈-map∘filter⁺  : f Preserves _≈₁_ ⟶ _≈₂_ →
                   ∃[ x ] x ∈₁ xs × y ≈₂ f x × P x →
                   y ∈₂ map f (filter P? xs)
  ∈-concatMap⁺   : Any ((y ∈_) ∘ f) xs → y ∈ concatMap f xs
  ∈-concatMap⁻   : y ∈ concatMap f xs → Any ((y ∈_) ∘ f) xs
  ∉[]            : x ∉ []
  deduplicate-∈⇔ : _≈_ Respectsʳ (flip R) → z ∈ xs ⇔ z ∈ deduplicate R? xs
  ```

* In `Data.List.Properties`:
  ```agda
  product≢0    : All NonZero ns → NonZero (product ns)
  ∈⇒≤product   : All NonZero ns → n ∈ ns → n ≤ product ns
  concat-[_]   : concat ∘ [_] ≗ id
  concatMap-++ : concatMap f (xs ++ ys) ≡ concatMap f xs ++ concatMap f ys
  filter-≐     : P ≐ Q → filter P? ≗ filter Q?

  partition-is-foldr : partition P? ≗ foldr (λ x → if does (P? x) then map₁ (x ∷_) else map₂ (x ∷_)) ([] , [])
  ```

* In `Data.List.Relation.Binary.Disjoint.Propositional.Properties`:
  ```agda
  deduplicate⁺ : Disjoint xs ys → Disjoint (deduplicate _≟_ xs) (deduplicate _≟_ ys)
  ```

* In `Data.List.Relation.Binary.Disjoint.Setoid.Properties`:
  ```agda
  deduplicate⁺ : Disjoint S xs ys → Disjoint S (deduplicate _≟_ xs) (deduplicate _≟_ ys)
  ```

* In `Data.List.Relation.Binary.Equality.Setoid`:
  ```agda
  ++⁺ˡ : ∀ xs → ys ≋ zs → xs ++ ys ≋ xs ++ zs
  ++⁺ʳ : ∀ zs → ws ≋ xs → ws ++ zs ≋ xs ++ zs
  ```

* In `Data.List.Relation.Binary.Permutation.Homogeneous`:
  ```agda
  steps : Permutation R xs ys → ℕ
  ```

* In `Data.List.Relation.Binary.Permutation.Propositional`:
  constructor aliases
  ```agda
  ↭-refl  : Reflexive _↭_
  ↭-prep  : ∀ x → xs ↭ ys → x ∷ xs ↭ x ∷ ys
  ↭-swap  : ∀ x y → xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys
  ```
  and properties
  ```agda
  ↭-reflexive-≋ : _≋_ ⇒ _↭_
  ↭⇒↭ₛ          : _↭_  ⇒ _↭ₛ_
  ↭ₛ⇒↭          : _↭ₛ_ ⇒ _↭_
  ```
  where `_↭ₛ_` is the `Setoid (setoid _)` instance of `Permutation`

* In `Data.List.Relation.Binary.Permutation.Propositional.Properties`:
  ```agda
  Any-resp-[σ∘σ⁻¹] : (σ : xs ↭ ys) (iy : Any P ys) →
                     Any-resp-↭ (trans (↭-sym σ) σ) iy ≡ iy
  ∈-resp-[σ∘σ⁻¹]   : (σ : xs ↭ ys) (iy : y ∈ ys) →
                     ∈-resp-↭ (trans (↭-sym σ) σ) iy ≡ iy
  product-↭        : product Preserves _↭_ ⟶ _≡_
  sum-↭ : sum Preserves _↭_ ⟶ _≡_
  ```

* In `Data.List.Relation.Binary.Permutation.Propositional.Properties.WithK`:
  ```agda
  dedup-++-↭ : Disjoint xs ys →
               deduplicate _≟_ (xs ++ ys) ↭ deduplicate _≟_ xs ++ deduplicate _≟_ ys
  ```

* In `Data.List.Relation.Binary.Permutation.Setoid`:
  ```agda
  ↭-reflexive-≋ : _≋_  ⇒ _↭_
  ↭-transˡ-≋    : LeftTrans _≋_ _↭_
  ↭-transʳ-≋    : RightTrans _↭_ _≋_
  ↭-trans′      : Transitive _↭_
  ```

* In `Data.List.Relation.Binary.Permutation.Setoid.Properties`:
  ```agda
  ↭-split : xs ↭ (as ++ [ v ] ++ bs) →
            ∃₂ λ ps qs → xs ≋ (ps ++ [ v ] ++ qs) × (ps ++ qs) ↭ (as ++ bs)
  drop-∷  : x ∷ xs ↭ x ∷ ys → xs ↭ ys
  ```

* In `Data.List.Relation.Binary.Pointwise`:
  ```agda
  ++⁺ˡ : Reflexive R → ∀ xs → (xs ++_) Preserves (Pointwise R) ⟶ (Pointwise R)
  ++⁺ʳ : Reflexive R → ∀ zs → (_++ zs) Preserves (Pointwise R) ⟶ (Pointwise R)
  ```

* In `Data.List.Relation.Binary.Sublist.Heterogeneous.Properties`:
  ```agda
  Sublist-[]-universal : Universal (Sublist R [])

  module ⊆-Reasoning (≲ : Preorder a e r)
  ```

* In `Data.List.Relation.Binary.Sublist.Propositional.Properties`:
  ```agda
  ⊆⇒⊆ₛ : (S : Setoid a ℓ) → as ⊆ bs → as (SetoidSublist.⊆ S) bs
  ```

* In `Data.List.Relation.Binary.Sublist.Setoid.Properties`:
  ```agda
  []⊆-universal : Universal ([] ⊆_)

  module ⊆-Reasoning

  concat⁺               : Sublist _⊆_ ass bss → concat ass ⊆ concat bss
  xs∈xss⇒xs⊆concat[xss] : xs ∈ xss → xs ⊆ concat xss
  all⊆concat            : (xss : List (List A)) → All (_⊆ concat xss) xss
  ```

* In `Data.List.Relation.Binary.Subset.Propositional.Properties`:
  ```agda
  ∷⊈[]   : x ∷ xs ⊈ []
  ⊆∷⇒∈∨⊆ : xs ⊆ y ∷ ys → y ∈ xs ⊎ xs ⊆ ys
  ⊆∷∧∉⇒⊆ : xs ⊆ y ∷ ys → y ∉ xs → xs ⊆ ys

  concatMap⁺ : xs ⊆ ys → concatMap f xs ⊆ concatMap f ys
  ```

* In `Data.List.Relation.Binary.Subset.Setoid.Properties`:
  ```agda
  ∷⊈[]   : x ∷ xs ⊈ []
  ⊆∷⇒∈∨⊆ : xs ⊆ y ∷ ys → y ∈ xs ⊎ xs ⊆ ys
  ⊆∷∧∉⇒⊆ : xs ⊆ y ∷ ys → y ∉ xs → xs ⊆ ys
  ```

* In `Data.List.Relation.Unary.First.Properties`:
  ```agda
  ¬First⇒All : ∁ Q ⊆ P → ∁ (First P Q) ⊆ All P
  ¬All⇒First : Decidable P → ∁ P ⊆ Q → ∁ (All P) ⊆ First P Q
  ```

* In `Data.List.Relation.Unary.All`:
  ```agda
  search : Decidable P → ∀ xs → All (∁ P) xs ⊎ Any P xs
  ```

* In `Data.List.Relation.Unary.All.Properties`:
  ```agda
  all⇒dropWhile≡[] : (P? : Decidable P) → All P xs → dropWhile P? xs ≡ []
  all⇒takeWhile≗id : (P? : Decidable P) → All P xs → takeWhile P? xs ≡ xs
  ```

* In `Data.List.Relation.Unary.Any.Properties`:
  ```agda
  concatMap⁺ : Any (Any P ∘ f) xs → Any P (concatMap f xs)
  concatMap⁻ : Any P (concatMap f xs) → Any (Any P ∘ f) xs
  ```

* In `Data.List.Relation.Unary.Unique.Propositional.Properties`:
  ```agda
  Unique[x∷xs]⇒x∉xs : Unique (x ∷ xs) → x ∉ xs
  ```

* In `Data.List.Relation.Unary.Unique.Setoid.Properties`:
  ```agda
  Unique[x∷xs]⇒x∉xs : Unique S (x ∷ xs) → x ∉ xs
  ```

* In `Data.Maybe.Properties`:
  ```agda
  maybe′-∘ : ∀ f g → f ∘ (maybe′ g b) ≗ maybe′ (f ∘ g) (f b)
  ```

* New lemmas in `Data.Nat.Properties`:
  ```agda
  m≤n⇒m≤n*o : ∀ o .{{_ : NonZero o}} → m ≤ n → m ≤ n * o
  m≤n⇒m≤o*n : ∀ o .{{_ : NonZero o}} → m ≤ n → m ≤ o * n
  <‴-irrefl : Irreflexive _≡_ _<‴_
  ≤‴-irrelevant : Irrelevant {A = ℕ} _≤‴_
  <‴-irrelevant : Irrelevant {A = ℕ} _<‴_
  >‴-irrelevant : Irrelevant {A = ℕ} _>‴_
  ≥‴-irrelevant : Irrelevant {A = ℕ} _≥‴_
  ```

  Added adjunction between `suc` and `pred`
  ```agda
  suc[m]≤n⇒m≤pred[n] : suc m ≤ n → m ≤ pred n
  m≤pred[n]⇒suc[m]≤n : .{{NonZero n}} → m ≤ pred n → suc m ≤ n
  ```

* In `Data.Product.Function.Dependent.Propositional`:
  ```agda
  congˡ : ∀ {k} → (∀ {x} → A x ∼[ k ] B x) → Σ I A ∼[ k ] Σ I B
  ```

* New lemmas in `Data.Rational.Properties`:
  ```agda
  nonNeg+nonNeg⇒nonNeg : ∀ p .{{_ : NonNegative p}} q .{{_ : NonNegative q}} → NonNegative (p + q)
  nonPos+nonPos⇒nonPos : ∀ p .{{_ : NonPositive p}} q .{{_ : NonPositive q}} → NonPositive (p + q)
  pos+nonNeg⇒pos : ∀ p .{{_ : Positive p}} q .{{_ : NonNegative q}} → Positive (p + q)
  nonNeg+pos⇒pos : ∀ p .{{_ : NonNegative p}} q .{{_ : Positive q}} → Positive (p + q)
  pos+pos⇒pos : ∀ p .{{_ : Positive p}} q .{{_ : Positive q}} → Positive (p + q)
  neg+nonPos⇒neg : ∀ p .{{_ : Negative p}} q .{{_ : NonPositive q}} → Negative (p + q)
  nonPos+neg⇒neg : ∀ p .{{_ : NonPositive p}} q .{{_ : Negative q}} → Negative (p + q)
  neg+neg⇒neg : ∀ p .{{_ : Negative p}} q .{{_ : Negative q}} → Negative (p + q)
  nonNeg*nonNeg⇒nonNeg : ∀ p .{{_ : NonNegative p}} q .{{_ : NonNegative q}} → NonNegative (p * q)
  nonPos*nonNeg⇒nonPos : ∀ p .{{_ : NonPositive p}} q .{{_ : NonNegative q}} → NonPositive (p * q)
  nonNeg*nonPos⇒nonPos : ∀ p .{{_ : NonNegative p}} q .{{_ : NonPositive q}} → NonPositive (p * q)
  nonPos*nonPos⇒nonPos : ∀ p .{{_ : NonPositive p}} q .{{_ : NonPositive q}} → NonNegative (p * q)
  pos*pos⇒pos : ∀ p .{{_ : Positive p}} q .{{_ : Positive q}} → Positive (p * q)
  neg*pos⇒neg : ∀ p .{{_ : Negative p}} q .{{_ : Positive q}} → Negative (p * q)
  pos*neg⇒neg : ∀ p .{{_ : Positive p}} q .{{_ : Negative q}} → Negative (p * q)
  neg*neg⇒pos : ∀ p .{{_ : Negative p}} q .{{_ : Negative q}} → Positive (p * q)
  ```

* New properties re-exported from `Data.Refinement`:
  ```agda
  value-injective : value v ≡ value w → v ≡ w
  _≟_             : DecidableEquality A → DecidableEquality [ x ∈ A ∣ P x ]
 ```

* New lemma in `Data.Vec.Properties`:
  ```agda
  map-concat : map f (concat xss) ≡ concat (map (map f) xss)
  ```

* New lemma in `Data.Vec.Relation.Binary.Equality.Cast`:
  ```agda
  ≈-cong′ : ∀ {f-len : ℕ → ℕ} (f : ∀ {n} → Vec A n → Vec B (f-len n))
    {m n} {xs : Vec A m} {ys : Vec A n} .{eq} →
    xs ≈[ eq ] ys → f xs ≈[ _ ] f ys
  ```

* In `Data.Vec.Relation.Binary.Equality.DecPropositional`:
  ```agda
  _≡?_ : DecidableEquality (Vec A n)
  ```

* In `Function.Related.TypeIsomorphisms`:
  ```agda
  Σ-distribˡ-⊎ : (∃ λ a → P a ⊎ Q a) ↔ (∃ P ⊎ ∃ Q)
  Σ-distribʳ-⊎ : (Σ (A ⊎ B) P) ↔ (Σ A (P ∘ inj₁) ⊎ Σ B (P ∘ inj₂))
  ×-distribˡ-⊎ : (A × (B ⊎ C)) ↔ (A × B ⊎ A × C)
  ×-distribʳ-⊎ : ((A ⊎ B) × C) ↔ (A × C ⊎ B × C)
  ∃-≡ : ∀ (P : A → Set b) {x} → P x ↔ (∃[ y ] y ≡ x × P y)
 ```

* In `Relation.Binary.Bundles`:
  ```agda
  record DecPreorder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂))
  ```
  plus associated sub-bundles.

* In `Relation.Binary.Construct.Interior.Symmetric`:
  ```agda
  decidable         : Decidable R → Decidable (SymInterior R)
  ```
  and for `Reflexive` and `Transitive` relations `R`:
  ```agda
  isDecEquivalence  : Decidable R → IsDecEquivalence (SymInterior R)
  isDecPreorder     : Decidable R → IsDecPreorder (SymInterior R) R
  isDecPartialOrder : Decidable R → IsDecPartialOrder (SymInterior R) R
  decPreorder       : Decidable R → DecPreorder _ _ _
  decPoset          : Decidable R → DecPoset _ _ _
  ```

* In `Relation.Binary.Structures`:
  ```agda
  record IsDecPreorder (_≲_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
    field
      isPreorder : IsPreorder _≲_
      _≟_        : Decidable _≈_
      _≲?_       : Decidable _≲_
  ```
  plus associated `isDecPreorder` fields in each higher `IsDec*Order` structure.

* In `Relation.Binary.Bundles` added `rawX` (e.g. `RawSetoid`) fields to each bundle.

* In `Relation.Nullary.Decidable`:
  ```agda
  does-⇔  : A ⇔ B → (a? : Dec A) → (b? : Dec B) → does a? ≡ does b?
  does-≡  : (a? b? : Dec A) → does a? ≡ does b?
  ```

* In `Relation.Nullary.Recomputable`:
  ```agda
  irrelevant-recompute : Recomputable (Irrelevant A)
  ```

* In `Relation.Unary.Properties`:
  ```agda
  map    : P ≐ Q → Decidable P → Decidable Q
  does-≐ : P ≐ Q → (P? : Decidable P) → (Q? : Decidable Q) → does ∘ P? ≗ does ∘ Q?
  does-≡ : (P? P?′ : Decidable P) → does ∘ P? ≗ does ∘ P?′
  ```
