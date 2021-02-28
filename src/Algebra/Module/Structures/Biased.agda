------------------------------------------------------------------------
-- The Agda standard library
--
-- This module provides alternative ways of providing instances of
-- structures in the Algebra.Module hierarchy.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; Setoid; IsEquivalence)

module Algebra.Module.Structures.Biased where

open import Algebra.Bundles
open import Algebra.Core
open import Algebra.Module.Consequences
open import Algebra.Module.Structures
open import Function.Base using (flip)
open import Level using (Level; _⊔_)

private
  variable
    m ℓm r ℓr s ℓs : Level
    M : Set m

module _ (commutativeSemiring : CommutativeSemiring r ℓr) where
  open CommutativeSemiring commutativeSemiring renaming (Carrier to R)

  -- A left semimodule over a commutative semiring is already a semimodule.

  record IsSemimoduleFromLeft (≈ᴹ : Rel {m} M ℓm) (+ᴹ : Op₂ M) (0ᴹ : M)
                              (*ₗ : Opₗ R M) : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    field
      isLeftSemimodule : IsLeftSemimodule semiring ≈ᴹ +ᴹ 0ᴹ *ₗ

    open IsLeftSemimodule isLeftSemimodule

    isBisemimodule : IsBisemimodule semiring semiring ≈ᴹ +ᴹ 0ᴹ *ₗ (flip *ₗ)
    isBisemimodule = record
      { +ᴹ-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
      ; isPreleftSemimodule = isPreleftSemimodule
      ; isPrerightSemimodule = record
        { *ᵣ-cong = flip *ₗ-cong
        ; *ᵣ-zeroʳ = *ₗ-zeroˡ
        ; *ᵣ-distribˡ = *ₗ-distribʳ
        ; *ᵣ-identityʳ = *ₗ-identityˡ
        ; *ᵣ-assoc =
          *ₗ-assoc+comm⇒*ᵣ-assoc _≈_ ≈ᴹ-setoid *ₗ-congʳ *ₗ-assoc *-comm
        ; *ᵣ-zeroˡ = *ₗ-zeroʳ
        ; *ᵣ-distribʳ = *ₗ-distribˡ
        }
      ; *ₗ-*ᵣ-assoc =
        *ₗ-assoc+comm⇒*ₗ-*ᵣ-assoc _≈_ ≈ᴹ-setoid *ₗ-congʳ *ₗ-assoc *-comm
      }

    isSemimodule : IsSemimodule commutativeSemiring ≈ᴹ +ᴹ 0ᴹ *ₗ (flip *ₗ)
    isSemimodule = record { isBisemimodule = isBisemimodule }

  -- Similarly, a right semimodule over a commutative semiring
  -- is already a semimodule.

  record IsSemimoduleFromRight (≈ᴹ : Rel {m} M ℓm) (+ᴹ : Op₂ M) (0ᴹ : M)
                               (*ᵣ : Opᵣ R M) : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    field
      isRightSemimodule : IsRightSemimodule semiring ≈ᴹ +ᴹ 0ᴹ *ᵣ

    open IsRightSemimodule isRightSemimodule

    isBisemimodule : IsBisemimodule semiring semiring ≈ᴹ +ᴹ 0ᴹ (flip *ᵣ) *ᵣ
    isBisemimodule = record
      { +ᴹ-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
      ; isPreleftSemimodule = record
        { *ₗ-cong = flip *ᵣ-cong
        ; *ₗ-zeroˡ = *ᵣ-zeroʳ
        ; *ₗ-distribʳ = *ᵣ-distribˡ
        ; *ₗ-identityˡ = *ᵣ-identityʳ
        ; *ₗ-assoc =
          *ᵣ-assoc+comm⇒*ₗ-assoc _≈_ ≈ᴹ-setoid *ᵣ-congˡ *ᵣ-assoc *-comm
        ; *ₗ-zeroʳ = *ᵣ-zeroˡ
        ; *ₗ-distribˡ = *ᵣ-distribʳ
        }
      ; isPrerightSemimodule = isPrerightSemimodule
      ; *ₗ-*ᵣ-assoc =
        *ᵣ-assoc+comm⇒*ₗ-*ᵣ-assoc _≈_ ≈ᴹ-setoid *ᵣ-congˡ *ᵣ-assoc *-comm
      }

    isSemimodule : IsSemimodule commutativeSemiring ≈ᴹ +ᴹ 0ᴹ (flip *ᵣ) *ᵣ
    isSemimodule = record { isBisemimodule = isBisemimodule }


module _ (commutativeRing : CommutativeRing r ℓr) where
  open CommutativeRing commutativeRing renaming (Carrier to R)

  -- A left module over a commutative ring is already a module.

  record IsModuleFromLeft (≈ᴹ : Rel {m} M ℓm)
                          (+ᴹ : Op₂ M) (0ᴹ : M) (-ᴹ : Op₁ M) (*ₗ : Opₗ R M)
                          : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    field
      isLeftModule : IsLeftModule ring ≈ᴹ +ᴹ 0ᴹ -ᴹ *ₗ

    open IsLeftModule isLeftModule

    isModule : IsModule commutativeRing ≈ᴹ +ᴹ 0ᴹ -ᴹ *ₗ (flip *ₗ)
    isModule = record
      { isBimodule = record
        { isBisemimodule = IsSemimoduleFromLeft.isBisemimodule
          {commutativeSemiring = commutativeSemiring}
          (record { isLeftSemimodule = isLeftSemimodule })
        ; -ᴹ‿cong = -ᴹ‿cong
        ; -ᴹ‿inverse = -ᴹ‿inverse
        }
      }

  -- Similarly, a right module over a commutative ring is already a module.

  record IsModuleFromRight (≈ᴹ : Rel {m} M ℓm)
                           (+ᴹ : Op₂ M) (0ᴹ : M) (-ᴹ : Op₁ M) (*ᵣ : Opᵣ R M)
                           : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    field
      isRightModule : IsRightModule ring ≈ᴹ +ᴹ 0ᴹ -ᴹ *ᵣ

    open IsRightModule isRightModule

    isModule : IsModule commutativeRing ≈ᴹ +ᴹ 0ᴹ -ᴹ (flip *ᵣ) *ᵣ
    isModule = record
      { isBimodule = record
        { isBisemimodule = IsSemimoduleFromRight.isBisemimodule
          {commutativeSemiring = commutativeSemiring}
          (record { isRightSemimodule = isRightSemimodule })
        ; -ᴹ‿cong = -ᴹ‿cong
        ; -ᴹ‿inverse = -ᴹ‿inverse
        }
      }
