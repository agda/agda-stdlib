------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundled definitions of homomorphisms between algebras
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Morphism.Bundles where

open import Algebra.Bundles -- using (Magma)
open import Algebra.Morphism.Structures -- using (IsMagmaHomomorphism)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.Morphism using (IsRelHomomorphism)
open import Relation.Binary.Morphism.Bundles using (SetoidHomomorphism)

private
  variable
    ℓ a ℓa b ℓb : Level


------------------------------------------------------------------------
-- Morphisms between Magmas
------------------------------------------------------------------------

record MagmaHomomorphism (A : Magma a ℓa) (B : Magma b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb) where
  private
    module A = Magma A
    module B = Magma B

  field
    ⟦_⟧ : A.Carrier → B.Carrier

    isMagmaHomomorphism : IsMagmaHomomorphism A.rawMagma B.rawMagma ⟦_⟧

  open IsMagmaHomomorphism isMagmaHomomorphism public

  setoidHomomorphism : SetoidHomomorphism A.setoid B.setoid
  setoidHomomorphism = record { isRelHomomorphism = isRelHomomorphism }

------------------------------------------------------------------------
-- Morphisms between Monoids
------------------------------------------------------------------------

record MonoidHomomorphism (A : Monoid a ℓa) (B : Monoid b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb) where
  private
    module A = Monoid A
    module B = Monoid B

  field
    ⟦_⟧ : A.Carrier → B.Carrier

    isMonoidHomomorphism : IsMonoidHomomorphism A.rawMonoid B.rawMonoid ⟦_⟧

  open IsMonoidHomomorphism isMonoidHomomorphism public

  magmaHomomorphism : MagmaHomomorphism A.magma B.magma
  magmaHomomorphism = record { isMagmaHomomorphism = isMagmaHomomorphism }

------------------------------------------------------------------------
-- Morphisms between Groups
------------------------------------------------------------------------

record GroupHomomorphism (A : Group a ℓa) (B : Group b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb) where
  private
    module A = Group A
    module B = Group B

  field
    ⟦_⟧ : A.Carrier → B.Carrier

    isGroupHomomorphism : IsGroupHomomorphism A.rawGroup B.rawGroup ⟦_⟧

  open IsGroupHomomorphism isGroupHomomorphism public

  monoidHomomorphism : MonoidHomomorphism A.monoid B.monoid
  monoidHomomorphism = record { isMonoidHomomorphism = isMonoidHomomorphism }

  open MonoidHomomorphism monoidHomomorphism public
    using (magmaHomomorphism)

------------------------------------------------------------------------
-- Morphisms between NearSemirings
------------------------------------------------------------------------

record NearSemiringHomomorphism (A : NearSemiring a ℓa) (B : NearSemiring b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb) where
  private
    module A = NearSemiring A
    module B = NearSemiring B

  field
    ⟦_⟧ : A.Carrier → B.Carrier

    isNearSemiringHomomorphism : IsNearSemiringHomomorphism A.rawNearSemiring B.rawNearSemiring ⟦_⟧

  open IsNearSemiringHomomorphism isNearSemiringHomomorphism public

  +-monoidHomomorphism : MonoidHomomorphism A.+-monoid B.+-monoid
  +-monoidHomomorphism = record { isMonoidHomomorphism = +-isMonoidHomomorphism }

  *-magmaHomomorphism : MagmaHomomorphism A.*-magma B.*-magma
  *-magmaHomomorphism = record { isMagmaHomomorphism = *-isMagmaHomomorphism }

  open MonoidHomomorphism +-monoidHomomorphism public
    renaming (magmaHomomorphism to +-magmaHomomorphism)

------------------------------------------------------------------------
-- Morphisms between Semirings
------------------------------------------------------------------------

record SemiringHomomorphism (A : Semiring a ℓa) (B : Semiring b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb) where
  private
    module A = Semiring A
    module B = Semiring B

  field
    ⟦_⟧ : A.Carrier → B.Carrier

    isSemiringHomomorphism : IsSemiringHomomorphism A.rawSemiring B.rawSemiring ⟦_⟧

  open IsSemiringHomomorphism isSemiringHomomorphism public

  nearSemiringHomomorphism : NearSemiringHomomorphism A.nearSemiring B.nearSemiring
  nearSemiringHomomorphism = record { isNearSemiringHomomorphism = isNearSemiringHomomorphism }

  open NearSemiringHomomorphism nearSemiringHomomorphism public
    using (*-magmaHomomorphism; +-monoidHomomorphism; +-magmaHomomorphism)

  *-monoidHomomorphism : MonoidHomomorphism A.*-monoid B.*-monoid
  *-monoidHomomorphism = record { isMonoidHomomorphism = *-isMonoidHomomorphism }

------------------------------------------------------------------------
-- Morphisms between KleeneAlgebras
------------------------------------------------------------------------

record KleeneAlgebraHomomorphism (A : KleeneAlgebra a ℓa) (B : KleeneAlgebra b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb) where
  private
    module A = KleeneAlgebra A
    module B = KleeneAlgebra B

  field
    ⟦_⟧ : A.Carrier → B.Carrier
    isKleeneAlgebraHomomorphism : IsKleeneAlgebraHomomorphism A.rawKleeneAlgebra B.rawKleeneAlgebra ⟦_⟧

  open IsKleeneAlgebraHomomorphism isKleeneAlgebraHomomorphism public

  semiringHomomorphism : SemiringHomomorphism A.semiring B.semiring
  semiringHomomorphism = record { isSemiringHomomorphism = isSemiringHomomorphism }

  open SemiringHomomorphism semiringHomomorphism public
    hiding (*-isMagmaHomomorphism; *-isMonoidHomomorphism)

------------------------------------------------------------------------
-- Morphisms between RingWithoutOnes
------------------------------------------------------------------------

record RingWithoutOneHomomorphism (A : RingWithoutOne a ℓa) (B : RingWithoutOne b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb) where
  private
    module A = RingWithoutOne A
    module B = RingWithoutOne B

  field
    ⟦_⟧ : A.Carrier → B.Carrier
    isRingWithoutOneHomomorphism : IsRingWithoutOneHomomorphism A.rawRingWithoutOne B.rawRingWithoutOne ⟦_⟧

  open IsRingWithoutOneHomomorphism isRingWithoutOneHomomorphism public

  nearSemiringHomomorphism : NearSemiringHomomorphism A.nearSemiring B.nearSemiring
  nearSemiringHomomorphism = record { isNearSemiringHomomorphism = isNearSemiringHomomorphism }

  open NearSemiringHomomorphism nearSemiringHomomorphism public
    using (*-magmaHomomorphism; +-magmaHomomorphism; +-monoidHomomorphism)

  +-groupHomomorphism : GroupHomomorphism A.+-group B.+-group
  +-groupHomomorphism = record { isGroupHomomorphism = +-isGroupHomomorphism }

------------------------------------------------------------------------
-- Morphisms between Rings
------------------------------------------------------------------------

record RingHomomorphism (A : Ring a ℓa) (B : Ring b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb) where
  private
    module A = Ring A
    module B = Ring B

  field
    ⟦_⟧ : A.Carrier → B.Carrier
    isRingHomomorphism : IsRingHomomorphism A.rawRing B.rawRing ⟦_⟧

  open IsRingHomomorphism isRingHomomorphism public

  +-groupHomomorphism : GroupHomomorphism A.+-group B.+-group
  +-groupHomomorphism = record { isGroupHomomorphism = +-isGroupHomomorphism }

  *-monoidHomomorphism : MonoidHomomorphism A.*-monoid B.*-monoid
  *-monoidHomomorphism = record { isMonoidHomomorphism = *-isMonoidHomomorphism }

------------------------------------------------------------------------
-- Morphisms between Quasigroups
------------------------------------------------------------------------

record QuasigroupHomomorphism (A : Quasigroup a ℓa) (B : Quasigroup b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb) where
  private
    module A = Quasigroup A
    module B = Quasigroup B

  field
    ⟦_⟧ : A.Carrier → B.Carrier
    isQuasigroupHomomorphism : IsQuasigroupHomomorphism A.rawQuasigroup B.rawQuasigroup ⟦_⟧

  open IsQuasigroupHomomorphism isQuasigroupHomomorphism public

  magmaHomomorphism : MagmaHomomorphism A.magma B.magma
  magmaHomomorphism = record { isMagmaHomomorphism = ∙-isMagmaHomomorphism }

------------------------------------------------------------------------
-- Morphisms between Loops
------------------------------------------------------------------------

record LoopHomomorphism (A : Loop a ℓa) (B : Loop b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb) where
  private
    module A = Loop A
    module B = Loop B

  field
    ⟦_⟧ : A.Carrier → B.Carrier
    isLoopHomomorphism : IsLoopHomomorphism A.rawLoop B.rawLoop ⟦_⟧

  open IsLoopHomomorphism isLoopHomomorphism public

  quasigroupHomomorphism : QuasigroupHomomorphism A.quasigroup B.quasigroup
  quasigroupHomomorphism = record { isQuasigroupHomomorphism = isQuasigroupHomomorphism }
