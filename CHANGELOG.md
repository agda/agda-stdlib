Version 2.2-dev
===============

The library has been tested using Agda 2.6.4.3.

Highlights
----------

Bug-fixes
---------

* Removed unnecessary parameter `#-trans : Transitive _#_` from
  `Relation.Binary.Reasoning.Base.Apartness`.

Non-backwards compatible changes
--------------------------------

Minor improvements
------------------

Deprecated modules
------------------

Deprecated names
----------------

* In `Algebra.Properties.CommutativeMagma.Divisibility`:
  ```agda
  ∣-factors    ↦  x|xy∧y|xy
  ∣-factors-≈  ↦  xy≈z⇒x|z∧y|z
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

* Bundled morphisms between (raw) algebraic structures:
  ```
  Algebra.Morphism.Bundles
  ```

* Properties of `IdempotentCommutativeMonoid`s refactored out from `Algebra.Solver.IdempotentCommutativeMonoid`:
  ```agda
  Algebra.Properties.IdempotentCommutativeMonoid
  ```

* Refactoring of the `Algebra.Solver.*Monoid` implementations, via
  a single `Solver` module API based on the existing `Expr`, and
  a common `Normal`-form API:
  ```agda
  Algebra.Solver.CommutativeMonoid.Normal
  Algebra.Solver.IdempotentCommutativeMonoid.Normal
  Algebra.Solver.Monoid.Expression
  Algebra.Solver.Monoid.Normal
  Algebra.Solver.Monoid.Solver
  ```

  NB Imports of the existing proof procedures `solve` and `prove` etc. should still be via the top-level interfaces in `Algebra.Solver.*Monoid`.

Additions to existing modules
-----------------------------

* In `Algebra.Bundles.KleeneAlgebra`:
  ```agda
  rawKleeneAlgebra : RawKleeneAlgebra _ _
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

* In `Algebra.Solver.Ring`
  ```agda
  Env : ℕ → Set _
  Env = Vec Carrier
 ```

* In `Algebra.Structures.RingWithoutOne`:
  ```agda
  isNearSemiring      : IsNearSemiring _ _
 ```

* In `Data.List.Properties`:
  ```agda
  product≢0 : All NonZero ns → NonZero (product ns)
  ∈⇒≤product : All NonZero ns → n ∈ ns → n ≤ product ns
  ```

* In `Data.List.Relation.Unary.All`:
  ```agda
  search : Decidable P → ∀ xs → All (∁ P) xs ⊎ Any P xs
  ```

* In `Data.List.Relation.Binary.Equality.Setoid`:
  ```agda
  ++⁺ʳ : ∀ xs → ys ≋ zs → xs ++ ys ≋ xs ++ zs
  ++⁺ˡ : ∀ zs → ws ≋ xs → ws ++ zs ≋ xs ++ zs
  ```

* In `Data.List.Relation.Binary.Pointwise`:
  ```agda
  ++⁺ʳ : Reflexive R → ∀ xs → (xs ++_) Preserves (Pointwise R) ⟶ (Pointwise R)
  ++⁺ˡ : Reflexive R → ∀ zs → (_++ zs) Preserves (Pointwise R) ⟶ (Pointwise R)
  ```

* In `Data.Maybe.Properties`:
  ```agda
  maybe′-∘ : ∀ f g → f ∘ (maybe′ g b) ≗ maybe′ (f ∘ g) (f b)
  ```

* New lemmas in `Data.Nat.Properties`:
  ```agda
  m≤n⇒m≤n*o : ∀ o .{{_ : NonZero o}} → m ≤ n → m ≤ n * o
  m≤n⇒m≤o*n : ∀ o .{{_ : NonZero o}} → m ≤ n → m ≤ o * n
  ```

  adjunction between `suc` and `pred`
  ```agda
  suc[m]≤n⇒m≤pred[n] : suc m ≤ n → m ≤ pred n
  m≤pred[n]⇒suc[m]≤n : .{{NonZero n}} → m ≤ pred n → suc m ≤ n
  ```

* New lemma in `Data.Vec.Properties`:
  ```agda
  map-concat : map f (concat xss) ≡ concat (map (map f) xss)
  ```

* In `Data.Vec.Relation.Binary.Equality.DecPropositional`:
  ```agda
  _≡?_ : DecidableEquality (Vec A n)
  ```

* In `Relation.Nullary.Decidable`:
  ```agda
  does-⇔  : A ⇔ B → (a? : Dec A) → (b? : Dec B) → does a? ≡ does b?
  does-≡  : (a? b? : Dec A) → does a? ≡ does b?
  ```

* In `Relation.Unary.Properties`:
  ```agda
  map    : P ≐ Q → Decidable P → Decidable Q
  does-≐ : P ≐ Q → (P? : Decidable P) → (Q? : Decidable Q) → does ∘ P? ≗ does ∘ Q?
  does-≡ : (P? P?′ : Decidable P) → does ∘ P? ≗ does ∘ P?′
  ```
