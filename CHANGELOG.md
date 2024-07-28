Version 2.2-dev
===============

The library has been tested using Agda 2.6.4.3.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Minor improvements
------------------

Deprecated modules
------------------

Deprecated names
----------------

New modules
-----------

* Bundled morphisms between (raw) algebraic structures:
  ```
  Algebra.Morphism.Bundles
  ```

Additions to existing modules
-----------------------------

* In `Algebra.Bundles.KleeneAlgebra`:
  ```agda
  rawKleeneAlgebra : RawKleeneAlgebra _ _
  ```

* In `Algebra.Bundles.Raw`
  ```agda
  record RawSuccessorSet c ℓ : Set (suc (c ⊔ ℓ))
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

* In `Algebra.Morphism.Structures`:
  ```agda
  module SuccessorSetMorphisms (N₁ : RawSuccessorSet a ℓ₁) (N₂ : RawSuccessorSet b ℓ₂) where
    record IsSuccessorSetHomomorphism (⟦_⟧ : N₁.Carrier → N₂.Carrier) : Set _
    record IsSuccessorSetMonomorphism (⟦_⟧ : N₁.Carrier → N₂.Carrier) : Set _
    record IsSuccessorSetIsomorphism  (⟦_⟧ : N₁.Carrier → N₂.Carrier) : Set _
  ```

* In `Algebra.Morphism.Structures.RingMorphisms`
  ```agda
  isRingWithoutOneHomomorphism : IsRingWithoutOneHomomorphism ⟦_⟧
  ```

* In `Algebra.Morphism.Structures.RingWithoutOneMorphisms`
  ```agda
  isNearSemiringHomomorphism : IsNearSemiringHomomorphism ⟦_⟧
  ```

* In `Algebra.Structures.RingWithoutOne`:
  ```agda
  isNearSemiring      : IsNearSemiring _ _
  ```
