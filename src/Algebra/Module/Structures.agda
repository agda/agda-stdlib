------------------------------------------------------------------------
-- The Agda standard library
--
-- Some algebraic structures defined over some other structure
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; Setoid; IsEquivalence)

module Algebra.Module.Structures where

open import Algebra.Bundles
open import Algebra.Core
import Algebra.Definitions as Defs
open import Algebra.Module.Definitions
open import Algebra.Structures
open import Data.Product using (_,_; proj₁; proj₂)
open import Level using (Level; _⊔_)

private
  variable
    m ℓm r ℓr s ℓs : Level
    M : Set m

module _ (semiring : Semiring r ℓr) (≈ᴹ : Rel {m} M ℓm) (+ᴹ : Op₂ M) (0ᴹ : M)
  where

  open Semiring semiring renaming (Carrier to R)

  record IsPreleftSemimodule (*ₗ : Opₗ R M) : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    open LeftDefs R ≈ᴹ
    field
      *ₗ-cong : Congruent _≈_ *ₗ
      *ₗ-zeroˡ : LeftZero 0# 0ᴹ *ₗ
      *ₗ-distribʳ : *ₗ DistributesOverʳ _+_ ⟶ +ᴹ
      *ₗ-identityˡ : LeftIdentity 1# *ₗ
      *ₗ-assoc : Associative _*_ *ₗ
      *ₗ-zeroʳ : RightZero 0ᴹ *ₗ
      *ₗ-distribˡ : *ₗ DistributesOverˡ +ᴹ

  record IsLeftSemimodule (*ₗ : Opₗ R M) : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    open LeftDefs R ≈ᴹ
    field
      +ᴹ-isCommutativeMonoid : IsCommutativeMonoid ≈ᴹ +ᴹ 0ᴹ
      isPreleftSemimodule : IsPreleftSemimodule *ₗ

    open IsPreleftSemimodule isPreleftSemimodule public

    open IsCommutativeMonoid +ᴹ-isCommutativeMonoid public
      using () renaming
      ( assoc                to +ᴹ-assoc
      ; comm                 to +ᴹ-comm
      ; identity             to +ᴹ-identity
      ; identityʳ            to +ᴹ-identityʳ
      ; identityˡ            to +ᴹ-identityˡ
      ; isEquivalence        to ≈ᴹ-isEquivalence
      ; isMagma              to +ᴹ-isMagma
      ; isMonoid             to +ᴹ-isMonoid
      ; isPartialEquivalence to ≈ᴹ-isPartialEquivalence
      ; isSemigroup          to +ᴹ-isSemigroup
      ; refl                 to ≈ᴹ-refl
      ; reflexive            to ≈ᴹ-reflexive
      ; setoid               to ≈ᴹ-setoid
      ; sym                  to ≈ᴹ-sym
      ; trans                to ≈ᴹ-trans
      ; ∙-cong               to +ᴹ-cong
      ; ∙-congʳ              to +ᴹ-congʳ
      ; ∙-congˡ              to +ᴹ-congˡ
      )

    *ₗ-congˡ : LeftCongruent *ₗ
    *ₗ-congˡ mm = *ₗ-cong refl mm

    *ₗ-congʳ : RightCongruent _≈_ *ₗ
    *ₗ-congʳ xx = *ₗ-cong xx ≈ᴹ-refl

  record IsPrerightSemimodule (*ᵣ : Opᵣ R M) : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    open RightDefs R ≈ᴹ
    field
      *ᵣ-cong : Congruent _≈_ *ᵣ
      *ᵣ-zeroʳ : RightZero 0# 0ᴹ *ᵣ
      *ᵣ-distribˡ : *ᵣ DistributesOverˡ _+_ ⟶ +ᴹ
      *ᵣ-identityʳ : RightIdentity 1# *ᵣ
      *ᵣ-assoc : Associative _*_ *ᵣ
      *ᵣ-zeroˡ : LeftZero 0ᴹ *ᵣ
      *ᵣ-distribʳ : *ᵣ DistributesOverʳ +ᴹ

  record IsRightSemimodule (*ᵣ : Opᵣ R M) : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    open RightDefs R ≈ᴹ
    field
      +ᴹ-isCommutativeMonoid : IsCommutativeMonoid ≈ᴹ +ᴹ 0ᴹ
      isPrerightSemimodule : IsPrerightSemimodule *ᵣ

    open IsPrerightSemimodule isPrerightSemimodule public

    open IsCommutativeMonoid +ᴹ-isCommutativeMonoid public
      using () renaming
      ( assoc                to +ᴹ-assoc
      ; comm                 to +ᴹ-comm
      ; identity             to +ᴹ-identity
      ; identityʳ            to +ᴹ-identityʳ
      ; identityˡ            to +ᴹ-identityˡ
      ; isEquivalence        to ≈ᴹ-isEquivalence
      ; isMagma              to +ᴹ-isMagma
      ; isMonoid             to +ᴹ-isMonoid
      ; isPartialEquivalence to ≈ᴹ-isPartialEquivalence
      ; isSemigroup          to +ᴹ-isSemigroup
      ; refl                 to ≈ᴹ-refl
      ; reflexive            to ≈ᴹ-reflexive
      ; setoid               to ≈ᴹ-setoid
      ; sym                  to ≈ᴹ-sym
      ; trans                to ≈ᴹ-trans
      ; ∙-cong               to +ᴹ-cong
      ; ∙-congʳ              to +ᴹ-congʳ
      ; ∙-congˡ              to +ᴹ-congˡ
      )

    *ᵣ-congˡ : LeftCongruent _≈_ *ᵣ
    *ᵣ-congˡ xx = *ᵣ-cong ≈ᴹ-refl xx

    *ᵣ-congʳ : RightCongruent *ᵣ
    *ᵣ-congʳ mm = *ᵣ-cong mm refl

module _ (R-semiring : Semiring r ℓr) (S-semiring : Semiring s ℓs)
         (≈ᴹ : Rel {m} M ℓm) (+ᴹ : Op₂ M) (0ᴹ : M)
  where

  open Semiring R-semiring using () renaming (Carrier to R)
  open Semiring S-semiring using () renaming (Carrier to S)

  record IsBisemimodule (*ₗ : Opₗ R M) (*ᵣ : Opᵣ S M)
                        : Set (r ⊔ s ⊔ m ⊔ ℓr ⊔ ℓs ⊔ ℓm) where
    open BiDefs R S ≈ᴹ
    field
      +ᴹ-isCommutativeMonoid : IsCommutativeMonoid ≈ᴹ +ᴹ 0ᴹ
      isPreleftSemimodule : IsPreleftSemimodule R-semiring ≈ᴹ +ᴹ 0ᴹ *ₗ
      isPrerightSemimodule : IsPrerightSemimodule S-semiring ≈ᴹ +ᴹ 0ᴹ *ᵣ
      *ₗ-*ᵣ-assoc : Associative *ₗ *ᵣ

    isLeftSemimodule : IsLeftSemimodule R-semiring ≈ᴹ +ᴹ 0ᴹ *ₗ
    isLeftSemimodule = record
      { +ᴹ-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
      ; isPreleftSemimodule = isPreleftSemimodule
      }

    isRightSemimodule : IsRightSemimodule S-semiring ≈ᴹ +ᴹ 0ᴹ *ᵣ
    isRightSemimodule = record
      { +ᴹ-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
      ; isPrerightSemimodule = isPrerightSemimodule
      }

    open IsLeftSemimodule isLeftSemimodule public
      hiding (+ᴹ-isCommutativeMonoid; isPreleftSemimodule)
    open IsPrerightSemimodule isPrerightSemimodule public
    open IsRightSemimodule isRightSemimodule public
      using (*ᵣ-congˡ; *ᵣ-congʳ)

module _ (commutativeSemiring : CommutativeSemiring r ℓr)
         (≈ᴹ : Rel {m} M ℓm) (+ᴹ : Op₂ M) (0ᴹ : M)
  where

  open CommutativeSemiring commutativeSemiring renaming (Carrier to R)

  -- An R-semimodule is an R-R-bisemimodule where R is commutative.
  -- This means that *ₗ and *ᵣ coincide up to mathematical equality, though it
  -- may be that they do not coincide up to definitional equality.

  record IsSemimodule (*ₗ : Opₗ R M) (*ᵣ : Opᵣ R M)
                      : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    field
      isBisemimodule : IsBisemimodule semiring semiring ≈ᴹ +ᴹ 0ᴹ *ₗ *ᵣ

    open IsBisemimodule isBisemimodule public


module _ (ring : Ring r ℓr)
         (≈ᴹ : Rel {m} M ℓm) (+ᴹ : Op₂ M) (0ᴹ : M) (-ᴹ : Op₁ M)
  where

  open Ring ring renaming (Carrier to R)

  record IsLeftModule (*ₗ : Opₗ R M) : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    open Defs ≈ᴹ
    field
      isLeftSemimodule : IsLeftSemimodule semiring ≈ᴹ +ᴹ 0ᴹ *ₗ
      -ᴹ‿cong : Congruent₁ -ᴹ
      -ᴹ‿inverse : Inverse 0ᴹ -ᴹ +ᴹ

    open IsLeftSemimodule isLeftSemimodule public

    +ᴹ-isAbelianGroup : IsAbelianGroup ≈ᴹ +ᴹ 0ᴹ -ᴹ
    +ᴹ-isAbelianGroup = record
      { isGroup = record
        { isMonoid = +ᴹ-isMonoid
        ; inverse = -ᴹ‿inverse
        ; ⁻¹-cong = -ᴹ‿cong
        }
      ; comm = +ᴹ-comm
      }

    open IsAbelianGroup +ᴹ-isAbelianGroup public
      using () renaming
      ( isGroup    to +ᴹ-isGroup
      ; inverseˡ   to -ᴹ‿inverseˡ
      ; inverseʳ   to -ᴹ‿inverseʳ
      ; uniqueˡ-⁻¹ to uniqueˡ‿-ᴹ
      ; uniqueʳ-⁻¹ to uniqueʳ‿-ᴹ
      )

  record IsRightModule (*ᵣ : Opᵣ R M) : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    open Defs ≈ᴹ
    field
      isRightSemimodule : IsRightSemimodule semiring ≈ᴹ +ᴹ 0ᴹ *ᵣ
      -ᴹ‿cong : Congruent₁ -ᴹ
      -ᴹ‿inverse : Inverse 0ᴹ -ᴹ +ᴹ

    open IsRightSemimodule isRightSemimodule public

    +ᴹ-isAbelianGroup : IsAbelianGroup ≈ᴹ +ᴹ 0ᴹ -ᴹ
    +ᴹ-isAbelianGroup = record
      { isGroup = record
        { isMonoid = +ᴹ-isMonoid
        ; inverse = -ᴹ‿inverse
        ; ⁻¹-cong = -ᴹ‿cong
        }
      ; comm = +ᴹ-comm
      }

    open IsAbelianGroup +ᴹ-isAbelianGroup public
      using () renaming
      ( isGroup    to +ᴹ-isGroup
      ; inverseˡ   to -ᴹ‿inverseˡ
      ; inverseʳ   to -ᴹ‿inverseʳ
      ; uniqueˡ-⁻¹ to uniqueˡ‿-ᴹ
      ; uniqueʳ-⁻¹ to uniqueʳ‿-ᴹ
      )

module _ (R-ring : Ring r ℓr) (S-ring : Ring s ℓs)
         (≈ᴹ : Rel {m} M ℓm) (+ᴹ : Op₂ M) (0ᴹ : M) (-ᴹ : Op₁ M)
  where

  open Ring R-ring renaming (Carrier to R; semiring to R-semiring)
  open Ring S-ring renaming (Carrier to S; semiring to S-semiring)

  record IsBimodule (*ₗ : Opₗ R M) (*ᵣ : Opᵣ S M)
                    : Set (r ⊔ s ⊔ m ⊔ ℓr ⊔ ℓs ⊔ ℓm) where
    open Defs ≈ᴹ
    field
      isBisemimodule : IsBisemimodule R-semiring S-semiring ≈ᴹ +ᴹ 0ᴹ *ₗ *ᵣ
      -ᴹ‿cong : Congruent₁ -ᴹ
      -ᴹ‿inverse : Inverse 0ᴹ -ᴹ +ᴹ

    open IsBisemimodule isBisemimodule public

    isLeftModule : IsLeftModule R-ring ≈ᴹ +ᴹ 0ᴹ -ᴹ *ₗ
    isLeftModule = record
      { isLeftSemimodule = isLeftSemimodule
      ; -ᴹ‿cong = -ᴹ‿cong
      ; -ᴹ‿inverse = -ᴹ‿inverse
      }

    open IsLeftModule isLeftModule public
      using ( +ᴹ-isAbelianGroup; +ᴹ-isGroup; -ᴹ‿inverseˡ; -ᴹ‿inverseʳ
            ; uniqueˡ‿-ᴹ; uniqueʳ‿-ᴹ)

    isRightModule : IsRightModule S-ring ≈ᴹ +ᴹ 0ᴹ -ᴹ *ᵣ
    isRightModule = record
      { isRightSemimodule = isRightSemimodule
      ; -ᴹ‿cong = -ᴹ‿cong
      ; -ᴹ‿inverse = -ᴹ‿inverse
      }

module _ (commutativeRing : CommutativeRing r ℓr)
         (≈ᴹ : Rel {m} M ℓm) (+ᴹ : Op₂ M) (0ᴹ : M) (-ᴹ : Op₁ M)
  where

  open CommutativeRing commutativeRing renaming (Carrier to R)

  -- An R-module is an R-R-bimodule where R is commutative.
  -- This means that *ₗ and *ᵣ coincide up to mathematical equality, though it
  -- may be that they do not coincide up to definitional equality.

  record IsModule (*ₗ : Opₗ R M) (*ᵣ : Opᵣ R M) : Set (r ⊔ m ⊔ ℓr ⊔ ℓm) where
    field
      isBimodule : IsBimodule ring ring ≈ᴹ +ᴹ 0ᴹ -ᴹ *ₗ *ᵣ

    open IsBimodule isBimodule public

    isSemimodule : IsSemimodule commutativeSemiring ≈ᴹ +ᴹ 0ᴹ *ₗ *ᵣ
    isSemimodule = record { isBisemimodule = isBisemimodule }
