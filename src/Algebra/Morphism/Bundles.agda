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

  open MagmaHomomorphism magmaHomomorphism public

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

  open MonoidHomomorphism +-monoidHomomorphism public

  *-magmaHomomorphism : MagmaHomomorphism A.*-magma B.*-magma
  *-magmaHomomorphism = record { isMagmaHomomorphism = *-isMagmaHomomorphism }

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

  *-monoidHomomorphism : MonoidHomomorphism A.*-monoid B.*-monoid
  *-monoidHomomorphism = record { isMonoidHomomorphism = *-isMonoidHomomorphism }

  open MonoidHomomorphism *-monoidHomomorphism public

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

  +-groupHomomorphism : GroupHomomorphism A.+-group B.+-group
  +-groupHomomorphism = record { isGroupHomomorphism = +-isGroupHomomorphism }

  open GroupHomomorphism +-groupHomomorphism public

  *-magmaHomomorphism : MagmaHomomorphism A.*-magma B.*-magma
  *-magmaHomomorphism = record { isMagmaHomomorphism = *-isMagmaHomomorphism }

  open MagmaHomomorphism *-magmaHomomorphism public
    hiding (setoidHomomorphism)

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

  open GroupHomomorphism +-groupHomomorphism public

  *-monoidHomomorphism : MonoidHomomorphism A.*-monoid B.*-monoid
  *-monoidHomomorphism = record { isMonoidHomomorphism = *-isMonoidHomomorphism }

