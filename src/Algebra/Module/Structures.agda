------------------------------------------------------------------------
-- The Agda standard library
--
-- Some algebraic structures defined over some other structure
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; Setoid; IsEquivalence)

module Algebra.Module.Structures
  {m ℓm} {M : Set m} (_≈ᴹ_ : Rel M ℓm)
  where

open import Algebra.Bundles
open import Algebra.FunctionProperties.Core
import Algebra.FunctionProperties as FP
import Algebra.FunctionProperties.Consequences as Consequences
import Algebra.FunctionProperties.LeftAction as L
import Algebra.FunctionProperties.RightAction as R
open import Algebra.Structures
open import Data.Product using (_,_; proj₁; proj₂)
open import Function.Base using (flip)
open import Level using (_⊔_)

module _ {r ℓr} (semiring : Semiring r ℓr) where
  open Semiring semiring renaming (Carrier to R)

  record IsPreleftSemimodule (+ᴹ : Op₂ M) (*ₗ : Opₗ R M) (0ᴹ : M)
                             : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    open L R _≈ᴹ_
    field
      *ₗ-cong : Congruent _≈_ *ₗ
      *ₗ-zeroˡ : LeftZero 0# 0ᴹ *ₗ
      *ₗ-distribʳ : *ₗ DistributesOverʳ _+_ ⟶ +ᴹ
      *ₗ-identityˡ : LeftIdentity 1# *ₗ
      *ₗ-assoc : Associative _*_ *ₗ
      *ₗ-zeroʳ : RightZero 0ᴹ *ₗ
      *ₗ-distribˡ : *ₗ DistributesOverˡ +ᴹ

  record IsLeftSemimodule (+ᴹ : Op₂ M) (*ₗ : Opₗ R M) (0ᴹ : M)
                          : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    open L R _≈ᴹ_
    field
      +ᴹ-isCommutativeMonoid : IsCommutativeMonoid _≈ᴹ_ +ᴹ 0ᴹ
      isPreleftSemimodule : IsPreleftSemimodule +ᴹ *ₗ 0ᴹ

    open IsPreleftSemimodule isPreleftSemimodule public

    open IsCommutativeMonoid +ᴹ-isCommutativeMonoid public
      using ()
      renaming ( assoc to +ᴹ-assoc; comm to +ᴹ-comm; identity to +ᴹ-identity
               ; identityʳ to +ᴹ-identityʳ; identityˡ to +ᴹ-identityˡ
               ; isEquivalence to M-isEquivalence; isMagma to +ᴹ-isMagma
               ; isMonoid to +ᴹ-isMonoid
               ; isPartialEquivalence to M-isPartialEquivalence
               ; isSemigroup to +ᴹ-isSemigroup; refl to M-refl
               ; reflexive to M-reflexive; setoid to M-setoid; sym to M-sym
               ; trans to M-trans; ∙-cong to +ᴹ-cong; ∙-congʳ to +ᴹ-congʳ
               ; ∙-congˡ to +ᴹ-congˡ)

  record IsPrerightSemimodule (+ᴹ : Op₂ M) (*ᵣ : Opᵣ R M) (0ᴹ : M)
                              : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    open R R _≈ᴹ_
    field
      *ᵣ-cong : Congruent _≈_ *ᵣ
      *ᵣ-zeroʳ : RightZero 0# 0ᴹ *ᵣ
      *ᵣ-distribˡ : *ᵣ DistributesOverˡ _+_ ⟶ +ᴹ
      *ᵣ-identityʳ : RightIdentity 1# *ᵣ
      *ᵣ-assoc : Associative _*_ *ᵣ
      *ᵣ-zeroˡ : LeftZero 0ᴹ *ᵣ
      *ᵣ-distribʳ : *ᵣ DistributesOverʳ +ᴹ

  record IsRightSemimodule (+ᴹ : Op₂ M) (*ᵣ : Opᵣ R M) (0ᴹ : M)
                           : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    open R R _≈ᴹ_
    field
      +ᴹ-isCommutativeMonoid : IsCommutativeMonoid _≈ᴹ_ +ᴹ 0ᴹ
      isPrerightSemimodule : IsPrerightSemimodule +ᴹ *ᵣ 0ᴹ

    open IsPrerightSemimodule isPrerightSemimodule public

    open IsCommutativeMonoid +ᴹ-isCommutativeMonoid public
      using ()
      renaming ( assoc to +ᴹ-assoc; comm to +ᴹ-comm; identity to +ᴹ-identity
               ; identityʳ to +ᴹ-identityʳ; identityˡ to +ᴹ-identityˡ
               ; isEquivalence to M-isEquivalence; isMagma to +ᴹ-isMagma
               ; isMonoid to +ᴹ-isMonoid
               ; isPartialEquivalence to M-isPartialEquivalence
               ; isSemigroup to +ᴹ-isSemigroup; refl to M-refl
               ; reflexive to M-reflexive; setoid to M-setoid; sym to M-sym
               ; trans to M-trans; ∙-cong to +ᴹ-cong; ∙-congʳ to +ᴹ-congʳ
               ; ∙-congˡ to +ᴹ-congˡ)

module _ {r s ℓr ℓs} (R-semiring : Semiring r ℓr) (S-semiring : Semiring s ℓs)
  where

  open Semiring R-semiring using () renaming (Carrier to R)
  open Semiring S-semiring using () renaming (Carrier to S)

  record IsBisemimodule (+ᴹ : Op₂ M) (*ₗ : Opₗ R M) (*ᵣ : Opᵣ S M) (0ᴹ : M)
                        : Set (r ⊔ s ⊔ m ⊔ ℓr ⊔ ℓs ⊔ ℓm) where
    field
      +ᴹ-isCommutativeMonoid : IsCommutativeMonoid _≈ᴹ_ +ᴹ 0ᴹ
      isPreleftSemimodule : IsPreleftSemimodule R-semiring +ᴹ *ₗ 0ᴹ
      isPrerightSemimodule : IsPrerightSemimodule S-semiring +ᴹ *ᵣ 0ᴹ
      *ₗ-*ᵣ-assoc : ∀ r m s → *ᵣ (*ₗ r m) s ≈ᴹ *ₗ r (*ᵣ m s)

    isLeftSemimodule : IsLeftSemimodule R-semiring +ᴹ *ₗ 0ᴹ
    isLeftSemimodule = record
      { +ᴹ-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
      ; isPreleftSemimodule = isPreleftSemimodule
      }

    isRightSemimodule : IsRightSemimodule S-semiring +ᴹ *ᵣ 0ᴹ
    isRightSemimodule = record
      { +ᴹ-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
      ; isPrerightSemimodule = isPrerightSemimodule
      }

    open IsLeftSemimodule isLeftSemimodule public
      hiding (+ᴹ-isCommutativeMonoid; isPreleftSemimodule)
    open IsPrerightSemimodule isPrerightSemimodule public

module _ {r ℓr} (commutativeSemiring : CommutativeSemiring r ℓr) where
  open CommutativeSemiring commutativeSemiring renaming (Carrier to R)

  record IsSemimodule (+ᴹ : Op₂ M) (*ₗ : Opₗ R M) (*ᵣ : Opᵣ R M) (0ᴹ : M)
                      : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    field
      isBisemimodule : IsBisemimodule semiring semiring +ᴹ *ₗ *ᵣ 0ᴹ

    open IsBisemimodule isBisemimodule public

  record IsSemimoduleFromLeft (+ᴹ : Op₂ M) (*ₗ : Opₗ R M) (0ᴹ : M)
                              : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    field
      isLeftSemimodule : IsLeftSemimodule semiring +ᴹ *ₗ 0ᴹ

    open IsLeftSemimodule isLeftSemimodule

    isSemimodule : IsSemimodule +ᴹ *ₗ (flip *ₗ) 0ᴹ
    isSemimodule = record
      { isBisemimodule = record
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
      }

    open IsSemimodule isSemimodule public
      hiding (isLeftSemimodule)

  record IsSemimoduleFromRight (+ᴹ : Op₂ M) (*ᵣ : Opᵣ R M) (0ᴹ : M)
                              : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    field
      isRightSemimodule : IsRightSemimodule semiring +ᴹ *ᵣ 0ᴹ

    open IsRightSemimodule isRightSemimodule

    isSemimodule : IsSemimodule +ᴹ (flip *ᵣ) *ᵣ 0ᴹ
    isSemimodule = record
      { isBisemimodule = record
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
      }

    open IsSemimodule isSemimodule public
      hiding (isRightSemimodule)


module _ {r ℓr} (ring : Ring r ℓr) where
  open Ring ring renaming (Carrier to R)

  record IsLeftModule (+ᴹ : Op₂ M) (*ₗ : Opₗ R M) (0ᴹ : M) (-ᴹ : Op₁ M)
                      : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    open FP _≈ᴹ_
    field
      isLeftSemimodule : IsLeftSemimodule semiring +ᴹ *ₗ 0ᴹ
      -ᴹ‿cong : Congruent₁ -ᴹ
      -ᴹ‿inverse : Inverse 0ᴹ -ᴹ +ᴹ

    open IsLeftSemimodule isLeftSemimodule public

    +ᴹ-isAbelianGroup : IsAbelianGroup _≈ᴹ_ +ᴹ 0ᴹ -ᴹ
    +ᴹ-isAbelianGroup = record
      { isGroup = record
        { isMonoid = +ᴹ-isMonoid
        ; inverse = -ᴹ‿inverse
        ; ⁻¹-cong = -ᴹ‿cong
        }
      ; comm = +ᴹ-comm
      }

    open IsAbelianGroup +ᴹ-isAbelianGroup public
      using ()
      renaming ( isGroup to +ᴹ-isGroup; inverseˡ to -ᴹ‿inverseˡ
               ; inverseʳ to -ᴹ‿inverseʳ ; uniqueˡ-⁻¹ to uniqueˡ‿-ᴹ
               ; uniqueʳ-⁻¹ to uniqueʳ‿-ᴹ)

  record IsRightModule (+ᴹ : Op₂ M) (*ᵣ : Opᵣ R M) (0ᴹ : M) (-ᴹ : Op₁ M)
                       : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    open FP _≈ᴹ_
    field
      isRightSemimodule : IsRightSemimodule semiring +ᴹ *ᵣ 0ᴹ
      -ᴹ‿cong : Congruent₁ -ᴹ
      -ᴹ‿inverse : Inverse 0ᴹ -ᴹ +ᴹ

    open IsRightSemimodule isRightSemimodule public

    +ᴹ-isAbelianGroup : IsAbelianGroup _≈ᴹ_ +ᴹ 0ᴹ -ᴹ
    +ᴹ-isAbelianGroup = record
      { isGroup = record
        { isMonoid = +ᴹ-isMonoid
        ; inverse = -ᴹ‿inverse
        ; ⁻¹-cong = -ᴹ‿cong
        }
      ; comm = +ᴹ-comm
      }

    open IsAbelianGroup +ᴹ-isAbelianGroup public
      using ()
      renaming ( isGroup to +ᴹ-isGroup; inverseˡ to -ᴹ‿inverseˡ
               ; inverseʳ to -ᴹ‿inverseʳ ; uniqueˡ-⁻¹ to uniqueˡ‿-ᴹ
               ; uniqueʳ-⁻¹ to uniqueʳ‿-ᴹ)

module _ {r s ℓr ℓs} (R-ring : Ring r ℓr) (S-ring : Ring s ℓs) where

  open Ring R-ring renaming (Carrier to R; semiring to R-semiring)
  open Ring S-ring renaming (Carrier to S; semiring to S-semiring)

  record IsBimodule (+ᴹ : Op₂ M) (*ₗ : Opₗ R M) (*ᵣ : Opᵣ S M) (0ᴹ : M)
                    (-ᴹ : Op₁ M) : Set (r ⊔ s ⊔ m ⊔ ℓr ⊔ ℓs ⊔ ℓm) where
    open FP _≈ᴹ_
    field
      isBisemimodule : IsBisemimodule R-semiring S-semiring +ᴹ *ₗ *ᵣ 0ᴹ
      -ᴹ‿cong : Congruent₁ -ᴹ
      -ᴹ‿inverse : Inverse 0ᴹ -ᴹ +ᴹ

    open IsBisemimodule isBisemimodule public

    isLeftModule : IsLeftModule R-ring +ᴹ *ₗ 0ᴹ -ᴹ
    isLeftModule = record
      { isLeftSemimodule = isLeftSemimodule
      ; -ᴹ‿cong = -ᴹ‿cong
      ; -ᴹ‿inverse = -ᴹ‿inverse
      }

    open IsLeftModule isLeftModule public
      using ( +ᴹ-isAbelianGroup; +ᴹ-isGroup; -ᴹ‿inverseˡ; -ᴹ‿inverseʳ
            ; uniqueˡ‿-ᴹ; uniqueʳ‿-ᴹ)

    isRightModule : IsRightModule S-ring +ᴹ *ᵣ 0ᴹ -ᴹ
    isRightModule = record
      { isRightSemimodule = isRightSemimodule
      ; -ᴹ‿cong = -ᴹ‿cong
      ; -ᴹ‿inverse = -ᴹ‿inverse
      }

module _ {r ℓr} (commutativeRing : CommutativeRing r ℓr) where
  open CommutativeRing commutativeRing renaming (Carrier to R)

  record IsModule (+ᴹ : Op₂ M) (*ₗ : Opₗ R M) (*ᵣ : Opᵣ R M) (0ᴹ : M)
                  (-ᴹ : Op₁ M) : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    field
      isBimodule : IsBimodule ring ring +ᴹ *ₗ *ᵣ 0ᴹ -ᴹ

    open IsBimodule isBimodule public

    isSemimodule : IsSemimodule commutativeSemiring +ᴹ *ₗ *ᵣ 0ᴹ
    isSemimodule = record { isBisemimodule = isBisemimodule }

  record IsModuleFromLeft (+ᴹ : Op₂ M) (*ₗ : Opₗ R M) (0ᴹ : M) (-ᴹ : Op₁ M)
                          : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    field
      isLeftModule : IsLeftModule ring +ᴹ *ₗ 0ᴹ -ᴹ

    open IsLeftModule isLeftModule

    isModule : IsModule +ᴹ *ₗ (flip *ₗ) 0ᴹ -ᴹ
    isModule = record
      { isBimodule = record
        { isBisemimodule = IsSemimoduleFromLeft.isBisemimodule
          {commutativeSemiring = commutativeSemiring}
          (record { isLeftSemimodule = isLeftSemimodule })
        ; -ᴹ‿cong = -ᴹ‿cong
        ; -ᴹ‿inverse = -ᴹ‿inverse
        }
      }

    open IsModule isModule public
      hiding (isLeftModule)

  record IsModuleFromRight (+ᴹ : Op₂ M) (*ᵣ : Opᵣ R M) (0ᴹ : M) (-ᴹ : Op₁ M)
                           : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    field
      isRightModule : IsRightModule ring +ᴹ *ᵣ 0ᴹ -ᴹ

    open IsRightModule isRightModule

    isModule : IsModule +ᴹ (flip *ᵣ) *ᵣ 0ᴹ -ᴹ
    isModule = record
      { isBimodule = record
        { isBisemimodule = IsSemimoduleFromRight.isBisemimodule
          {commutativeSemiring = commutativeSemiring}
          (record { isRightSemimodule = isRightSemimodule })
        ; -ᴹ‿cong = -ᴹ‿cong
        ; -ᴹ‿inverse = -ᴹ‿inverse
        }
      }

    open IsModule isModule public
      hiding (isRightModule)
