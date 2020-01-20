------------------------------------------------------------------------
-- The Agda standard library
--
-- Abbreviations of some of the module-like definitions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; Setoid; IsEquivalence)

module Algebra.Module.Structures.Biased
  {m ℓm} {M : Set m} (_≈ᴹ_ : Rel M ℓm)
  where

open import Algebra.Bundles
open import Algebra.Core
open import Algebra.Module.Structures _≈ᴹ_
open import Function.Base using (flip)
open import Level using (_⊔_)

module _ {r ℓr} (commutativeSemiring : CommutativeSemiring r ℓr) where
  open CommutativeSemiring commutativeSemiring renaming (Carrier to R)

  record IsSemimoduleFromLeft (+ᴹ : Op₂ M) (*ₗ : Opₗ R M) (0ᴹ : M)
                              : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    field
      isLeftSemimodule : IsLeftSemimodule semiring +ᴹ *ₗ 0ᴹ

    open IsLeftSemimodule isLeftSemimodule

    isBisemimodule : IsBisemimodule semiring semiring +ᴹ *ₗ (flip *ₗ) 0ᴹ
    isBisemimodule = record
      { +ᴹ-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
      ; isPreleftSemimodule = isPreleftSemimodule
      ; isPrerightSemimodule = record
        { *ᵣ-cong = flip *ₗ-cong
        ; *ᵣ-zeroʳ = *ₗ-zeroˡ
        ; *ᵣ-distribˡ = *ₗ-distribʳ
        ; *ᵣ-identityʳ = *ₗ-identityˡ
        ; *ᵣ-assoc = λ m r s → M-trans (M-sym (*ₗ-assoc s r m))
                                       (*ₗ-cong (*-comm s r) M-refl)
        ; *ᵣ-zeroˡ = *ₗ-zeroʳ
        ; *ᵣ-distribʳ = *ₗ-distribˡ
        }
      ; *ₗ-*ᵣ-assoc = λ r m s →
        M-trans (M-sym (*ₗ-assoc s r m))
                (M-trans (*ₗ-cong (*-comm s r) M-refl)
                         (*ₗ-assoc r s m))
      }

    isSemimodule : IsSemimodule commutativeSemiring +ᴹ *ₗ (flip *ₗ) 0ᴹ
    isSemimodule = record { isBisemimodule = isBisemimodule }

  record IsSemimoduleFromRight (+ᴹ : Op₂ M) (*ᵣ : Opᵣ R M) (0ᴹ : M)
                              : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    field
      isRightSemimodule : IsRightSemimodule semiring +ᴹ *ᵣ 0ᴹ

    open IsRightSemimodule isRightSemimodule

    isBisemimodule : IsBisemimodule semiring semiring +ᴹ (flip *ᵣ) *ᵣ 0ᴹ
    isBisemimodule = record
      { +ᴹ-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
      ; isPreleftSemimodule = record
        { *ₗ-cong = flip *ᵣ-cong
        ; *ₗ-zeroˡ = *ᵣ-zeroʳ
        ; *ₗ-distribʳ = *ᵣ-distribˡ
        ; *ₗ-identityˡ = *ᵣ-identityʳ
        ; *ₗ-assoc = λ r s m → M-trans (*ᵣ-cong M-refl (*-comm r s))
                                       (M-sym (*ᵣ-assoc m s r))
        ; *ₗ-zeroʳ = *ᵣ-zeroˡ
        ; *ₗ-distribˡ = *ᵣ-distribʳ
        }
      ; isPrerightSemimodule = isPrerightSemimodule
      ; *ₗ-*ᵣ-assoc = λ r m s →
        M-trans (*ᵣ-assoc m r s)
                (M-trans (*ᵣ-cong M-refl (*-comm r s))
                         (M-sym (*ᵣ-assoc m s r)))
      }

    isSemimodule : IsSemimodule commutativeSemiring +ᴹ (flip *ᵣ) *ᵣ 0ᴹ
    isSemimodule = record { isBisemimodule = isBisemimodule }


module _ {r ℓr} (commutativeRing : CommutativeRing r ℓr) where
  open CommutativeRing commutativeRing renaming (Carrier to R)

  record IsModuleFromLeft (+ᴹ : Op₂ M) (*ₗ : Opₗ R M) (0ᴹ : M) (-ᴹ : Op₁ M)
                          : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    field
      isLeftModule : IsLeftModule ring +ᴹ *ₗ 0ᴹ -ᴹ

    open IsLeftModule isLeftModule

    isModule : IsModule commutativeRing +ᴹ *ₗ (flip *ₗ) 0ᴹ -ᴹ
    isModule = record
      { isBimodule = record
        { isBisemimodule = IsSemimoduleFromLeft.isBisemimodule
          {commutativeSemiring = commutativeSemiring}
          (record { isLeftSemimodule = isLeftSemimodule })
        ; -ᴹ‿cong = -ᴹ‿cong
        ; -ᴹ‿inverse = -ᴹ‿inverse
        }
      }

  record IsModuleFromRight (+ᴹ : Op₂ M) (*ᵣ : Opᵣ R M) (0ᴹ : M) (-ᴹ : Op₁ M)
                           : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    field
      isRightModule : IsRightModule ring +ᴹ *ᵣ 0ᴹ -ᴹ

    open IsRightModule isRightModule

    isModule : IsModule commutativeRing +ᴹ (flip *ᵣ) *ᵣ 0ᴹ -ᴹ
    isModule = record
      { isBimodule = record
        { isBisemimodule = IsSemimoduleFromRight.isBisemimodule
          {commutativeSemiring = commutativeSemiring}
          (record { isRightSemimodule = isRightSemimodule })
        ; -ᴹ‿cong = -ᴹ‿cong
        ; -ᴹ‿inverse = -ᴹ‿inverse
        }
      }
