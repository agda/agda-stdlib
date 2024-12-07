------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundled definitions of homomorphisms between algebras
--
-- NB indexed by Raw bundles, just as IsXHomomorphism is
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Morphism.Bundles where

open import Algebra.Bundles.Raw
open import Algebra.Morphism.Structures
open import Level using (Level; suc; _⊔_)
--open import Relation.Binary.Morphism using (IsRelHomomorphism)
--open import Relation.Binary.Morphism.Bundles using (SetoidHomomorphism)

private
  variable
    ℓ a ℓa b ℓb : Level


------------------------------------------------------------------------
-- Morphisms between Magmas
------------------------------------------------------------------------

record MagmaHomomorphism
  (A : RawMagma a ℓa) (B : RawMagma b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb)
  where
  private
    module A = RawMagma A
    module B = RawMagma B

  field
    ⟦_⟧ : A.Carrier → B.Carrier

    isMagmaHomomorphism : IsMagmaHomomorphism A B ⟦_⟧

  open IsMagmaHomomorphism isMagmaHomomorphism public

------------------------------------------------------------------------
-- Morphisms between Monoids
------------------------------------------------------------------------

record MonoidHomomorphism
  (A : RawMonoid a ℓa) (B : RawMonoid b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb)
  where
  private
    module A = RawMonoid A
    module B = RawMonoid B

  field
    ⟦_⟧ : A.Carrier → B.Carrier

    isMonoidHomomorphism : IsMonoidHomomorphism A B ⟦_⟧

  open IsMonoidHomomorphism isMonoidHomomorphism public

  magmaHomomorphism : MagmaHomomorphism A.rawMagma B.rawMagma
  magmaHomomorphism = record { isMagmaHomomorphism = isMagmaHomomorphism }

------------------------------------------------------------------------
-- Morphisms between Groups
------------------------------------------------------------------------

record GroupHomomorphism
  (A : RawGroup a ℓa) (B : RawGroup b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb)
  where
  private
    module A = RawGroup A
    module B = RawGroup B

  field
    ⟦_⟧ : A.Carrier → B.Carrier

    isGroupHomomorphism : IsGroupHomomorphism A B ⟦_⟧

  open IsGroupHomomorphism isGroupHomomorphism public

  monoidHomomorphism : MonoidHomomorphism A.rawMonoid B.rawMonoid
  monoidHomomorphism = record { isMonoidHomomorphism = isMonoidHomomorphism }

  open MonoidHomomorphism monoidHomomorphism public
    using (magmaHomomorphism)

------------------------------------------------------------------------
-- Morphisms between NearSemirings
------------------------------------------------------------------------

record NearSemiringHomomorphism
  (A : RawNearSemiring a ℓa) (B : RawNearSemiring b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb)
  where
  private
    module A = RawNearSemiring A
    module B = RawNearSemiring B

  field
    ⟦_⟧ : A.Carrier → B.Carrier

    isNearSemiringHomomorphism : IsNearSemiringHomomorphism A B ⟦_⟧

  open IsNearSemiringHomomorphism isNearSemiringHomomorphism public

  +-monoidHomomorphism : MonoidHomomorphism A.+-rawMonoid B.+-rawMonoid
  +-monoidHomomorphism = record { isMonoidHomomorphism = +-isMonoidHomomorphism }

  *-magmaHomomorphism : MagmaHomomorphism A.*-rawMagma B.*-rawMagma
  *-magmaHomomorphism = record { isMagmaHomomorphism = *-isMagmaHomomorphism }

  open MonoidHomomorphism +-monoidHomomorphism public
    using ()
    renaming (magmaHomomorphism to +-magmaHomomorphism)

------------------------------------------------------------------------
-- Morphisms between Semirings
------------------------------------------------------------------------

record SemiringHomomorphism
  (A : RawSemiring a ℓa) (B : RawSemiring b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb)
  where
  private
    module A = RawSemiring A
    module B = RawSemiring B

  field
    ⟦_⟧ : A.Carrier → B.Carrier

    isSemiringHomomorphism : IsSemiringHomomorphism A B ⟦_⟧

  open IsSemiringHomomorphism isSemiringHomomorphism public

  nearSemiringHomomorphism : NearSemiringHomomorphism A.rawNearSemiring B.rawNearSemiring
  nearSemiringHomomorphism = record { isNearSemiringHomomorphism = isNearSemiringHomomorphism }

  open NearSemiringHomomorphism nearSemiringHomomorphism public
    using (*-magmaHomomorphism; +-monoidHomomorphism; +-magmaHomomorphism)

  *-monoidHomomorphism : MonoidHomomorphism A.*-rawMonoid B.*-rawMonoid
  *-monoidHomomorphism = record { isMonoidHomomorphism = *-isMonoidHomomorphism }

------------------------------------------------------------------------
-- Morphisms between KleeneAlgebras
------------------------------------------------------------------------

record KleeneAlgebraHomomorphism
  (A : RawKleeneAlgebra a ℓa) (B : RawKleeneAlgebra b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb)
  where
  private
    module A = RawKleeneAlgebra A
    module B = RawKleeneAlgebra B

  field
    ⟦_⟧ : A.Carrier → B.Carrier
    isKleeneAlgebraHomomorphism : IsKleeneAlgebraHomomorphism A B ⟦_⟧

  open IsKleeneAlgebraHomomorphism isKleeneAlgebraHomomorphism public

  semiringHomomorphism : SemiringHomomorphism A.rawSemiring B.rawSemiring
  semiringHomomorphism = record { isSemiringHomomorphism = isSemiringHomomorphism }

  open SemiringHomomorphism semiringHomomorphism public
    hiding (*-isMagmaHomomorphism; *-isMonoidHomomorphism)

------------------------------------------------------------------------
-- Morphisms between RingWithoutOnes
------------------------------------------------------------------------

record RingWithoutOneHomomorphism (A : RawRingWithoutOne a ℓa) (B : RawRingWithoutOne b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb) where
  private
    module A = RawRingWithoutOne A
    module B = RawRingWithoutOne B

  field
    ⟦_⟧ : A.Carrier → B.Carrier
    isRingWithoutOneHomomorphism : IsRingWithoutOneHomomorphism A B ⟦_⟧

  open IsRingWithoutOneHomomorphism isRingWithoutOneHomomorphism public

  nearSemiringHomomorphism : NearSemiringHomomorphism A.rawNearSemiring B.rawNearSemiring
  nearSemiringHomomorphism = record { isNearSemiringHomomorphism = isNearSemiringHomomorphism }

  open NearSemiringHomomorphism nearSemiringHomomorphism public
    using (*-magmaHomomorphism; +-magmaHomomorphism; +-monoidHomomorphism)

  +-groupHomomorphism : GroupHomomorphism A.+-rawGroup B.+-rawGroup
  +-groupHomomorphism = record { isGroupHomomorphism = +-isGroupHomomorphism }

------------------------------------------------------------------------
-- Morphisms between Rings
------------------------------------------------------------------------

record RingHomomorphism (A : RawRing a ℓa) (B : RawRing b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb) where
  private
    module A = RawRing A
    module B = RawRing B

  field
    ⟦_⟧ : A.Carrier → B.Carrier
    isRingHomomorphism : IsRingHomomorphism A B ⟦_⟧

  open IsRingHomomorphism isRingHomomorphism public

  ringWithoutOneHomomorphism : RingWithoutOneHomomorphism A.rawRingWithoutOne B.rawRingWithoutOne
  ringWithoutOneHomomorphism = record { isRingWithoutOneHomomorphism = isRingWithoutOneHomomorphism }

  open RingWithoutOneHomomorphism ringWithoutOneHomomorphism public
    using (+-groupHomomorphism)

  semiringHomomorphism : SemiringHomomorphism A.rawSemiring B.rawSemiring
  semiringHomomorphism = record { isSemiringHomomorphism = isSemiringHomomorphism }

  open SemiringHomomorphism semiringHomomorphism public
    using ( nearSemiringHomomorphism
          ; *-monoidHomomorphism; *-magmaHomomorphism
          ; +-monoidHomomorphism; +-magmaHomomorphism)

------------------------------------------------------------------------
-- Morphisms between Quasigroups
------------------------------------------------------------------------

record QuasigroupHomomorphism
  (A : RawQuasigroup a ℓa) (B : RawQuasigroup b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb)
  where
  private
    module A = RawQuasigroup A
    module B = RawQuasigroup B

  field
    ⟦_⟧ : A.Carrier → B.Carrier
    isQuasigroupHomomorphism : IsQuasigroupHomomorphism A B ⟦_⟧

  open IsQuasigroupHomomorphism isQuasigroupHomomorphism public

  magmaHomomorphism : MagmaHomomorphism A.∙-rawMagma B.∙-rawMagma
  magmaHomomorphism = record { isMagmaHomomorphism = ∙-isMagmaHomomorphism }

------------------------------------------------------------------------
-- Morphisms between Loops
------------------------------------------------------------------------

record LoopHomomorphism
  (A : RawLoop a ℓa) (B : RawLoop b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb)
  where
  private
    module A = RawLoop A
    module B = RawLoop B

  field
    ⟦_⟧ : A.Carrier → B.Carrier
    isLoopHomomorphism : IsLoopHomomorphism A B ⟦_⟧

  open IsLoopHomomorphism isLoopHomomorphism public

  quasigroupHomomorphism : QuasigroupHomomorphism A.rawQuasigroup B.rawQuasigroup
  quasigroupHomomorphism = record { isQuasigroupHomomorphism = isQuasigroupHomomorphism }

