------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties for the functional vector algebra approach
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Functional.Algebra.Properties where

open import Level using (Level; _⊔_)
open import Function using (_$_; flip)
open import Data.Product hiding (map)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Function.Base using (_∘′_; _ˢ_; _∘_)
open import Data.Vec.Functional
open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Module
open import Algebra.Module.Structures
open import Relation.Binary
import Algebra.Definitions as Definitions
open import Algebra.Structures
open import Data.Vec.Functional.Algebra.Base
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as Pointwise

private variable
  a ℓ : Level
  A : Set ℓ
  n : ℕ

------------------------------------------------------------------------
-- Raw structure properties

module RawMagmaProperties (rawMagma : RawMagma a ℓ) (n : ℕ) where
  private
    magmaᵛ = rawMagmaᵛ rawMagma n
    module VM = RawMagma magmaᵛ
    module M = RawMagma rawMagma

  open IsEquivalence

  isMagmaᵛ : IsMagma M._≈_ M._∙_ → IsMagma VM._≈_ VM._∙_
  isMagmaᵛ base = record
    { isEquivalence = flip Pointwise.isEquivalence _ B.isEquivalence
    ; ∙-cong        = λ x≈y u≈v i → B.∙-cong (x≈y i) (u≈v i)
    }
    where module B = IsMagma base

  isCommutativeMagmaᵛ : IsCommutativeMagma M._≈_ M._∙_ → IsCommutativeMagma VM._≈_ VM._∙_
  isCommutativeMagmaᵛ base = record
    { isMagma = isMagmaᵛ CM.isMagma
    ; comm    = λ xs ys i → CM.comm (xs i) (ys i)
    }
    where module CM = IsCommutativeMagma base

  isSemigroupᵛ : IsSemigroup M._≈_ M._∙_ → IsSemigroup VM._≈_ VM._∙_
  isSemigroupᵛ base = record
    { isMagma = isMagmaᵛ SG.isMagma
    ; assoc   = λ xs ys zs i → SG.assoc (xs i) (ys i) (zs i)
    }
    where module SG = IsSemigroup base

  isCommutativeSemigroupᵛ : IsCommutativeSemigroup M._≈_ M._∙_ → IsCommutativeSemigroup VM._≈_ VM._∙_
  isCommutativeSemigroupᵛ base = record
    { isSemigroup = isSemigroupᵛ CS.isSemigroup
    ; comm        = λ xs ys i → CS.comm (xs i) (ys i)
    }
    where module CS = IsCommutativeSemigroup base

------------------------------------------------------------------------

module RawMonoidProperties (rawMonoid : RawMonoid a ℓ) (n : ℕ) where
  private
    monoidᵛ = rawMonoidᵛ rawMonoid n
    module VM = RawMonoid monoidᵛ
    module RM = RawMonoid rawMonoid

  open RawMagmaProperties (RawMonoid.rawMagma rawMonoid) n public

  private
    module ≈ = Definitions RM._≈_
    module ≈ᴹ = Definitions VM._≈_

  +ᴹ-identityˡ : ≈.LeftIdentity RM.ε RM._∙_ → ≈ᴹ.LeftIdentity VM.ε VM._∙_
  +ᴹ-identityˡ idˡ xs i = idˡ (xs i)

  +ᴹ-identityʳ : ≈.RightIdentity RM.ε RM._∙_ → ≈ᴹ.RightIdentity VM.ε VM._∙_
  +ᴹ-identityʳ idʳ xs i = idʳ (xs i)

  +ᴹ-identity : ≈.Identity RM.ε RM._∙_ → ≈ᴹ.Identity VM.ε VM._∙_
  +ᴹ-identity (idˡ , idʳ) = +ᴹ-identityˡ idˡ , +ᴹ-identityʳ idʳ

  isMonoidᵛ : IsMonoid RM._≈_ RM._∙_ RM.ε → IsMonoid VM._≈_ VM._∙_ VM.ε
  isMonoidᵛ isMonoid = record
    { isSemigroup = isSemigroupᵛ M.isSemigroup
    ; identity = +ᴹ-identity M.identity
    } where module M = IsMonoid isMonoid

  isCommutativeMonoidᵛ : IsCommutativeMonoid RM._≈_ RM._∙_ RM.ε → IsCommutativeMonoid VM._≈_ VM._∙_ VM.ε
  isCommutativeMonoidᵛ base = record
    { isMonoid = isMonoidᵛ CM.isMonoid
    ; comm     = λ xs ys i → CM.comm (xs i) (ys i)
    } where module CM = IsCommutativeMonoid base

------------------------------------------------------------------------

module RawGroupProperties (rawGroup : RawGroup a ℓ) (n : ℕ) where
  private
    groupᵛ = rawGroupᵛ rawGroup n
    module RG = RawGroup groupᵛ
    module G = RawGroup rawGroup
  open RawMonoidProperties (RawGroup.rawMonoid rawGroup) n public

  private
    module ≈ = Definitions G._≈_
    module ≈ᴹ = Definitions RG._≈_

  -ᴹ‿inverseˡ : ≈.LeftInverse G.ε G._⁻¹ G._∙_ → ≈ᴹ.LeftInverse RG.ε RG._⁻¹ RG._∙_
  -ᴹ‿inverseˡ -‿inverseˡ xs i = -‿inverseˡ (xs i)

  -ᴹ‿inverseʳ : ≈.RightInverse G.ε G._⁻¹ G._∙_ → ≈ᴹ.RightInverse RG.ε RG._⁻¹ RG._∙_
  -ᴹ‿inverseʳ -‿inverseʳ xs i = -‿inverseʳ (xs i)

  -ᴹ‿inverse : ≈.Inverse G.ε G._⁻¹ G._∙_ → ≈ᴹ.Inverse RG.ε RG._⁻¹ RG._∙_
  -ᴹ‿inverse (-‿inverseˡ , -‿inverseʳ) = -ᴹ‿inverseˡ -‿inverseˡ , -ᴹ‿inverseʳ -‿inverseʳ

  -ᴹ‿cong : ≈.Congruent₁ G._⁻¹ → ≈ᴹ.Congruent₁ RG._⁻¹
  -ᴹ‿cong -‿cong xs≈ys i = -‿cong (xs≈ys i)

  isGroupᵛ : IsGroup G._≈_ G._∙_ G.ε G._⁻¹ → IsGroup RG._≈_ RG._∙_ RG.ε RG._⁻¹
  isGroupᵛ isGroup = record
    { isMonoid = isMonoidᵛ M.isMonoid
    ; inverse = -ᴹ‿inverse M.inverse
    ; ⁻¹-cong = -ᴹ‿cong M.⁻¹-cong
    } where module M = IsGroup isGroup

  isAbelianGroupᵛ : IsAbelianGroup G._≈_ G._∙_ G.ε G._⁻¹ → IsAbelianGroup RG._≈_ RG._∙_ RG.ε RG._⁻¹
  isAbelianGroupᵛ base = record
    { isGroup = isGroupᵛ AG.isGroup
    ; comm    = λ xs ys i → AG.comm (xs i) (ys i)
    }
    where module AG = IsAbelianGroup base

------------------------------------------------------------------------

module VecSemiringProperties (rawSemiring : RawSemiring a ℓ) (n : ℕ) where
  private
    module SR  = RawSemiring rawSemiring
    rawNearSemiring = SR.rawNearSemiring
    module NS  = RawNearSemiring rawNearSemiring
    nearSemiringᵛ = rawNearSemiringᵛ rawNearSemiring n
    module RNS = RawNearSemiring nearSemiringᵛ
    leftSemiᵛ  = rawLeftSemimoduleᵛ  rawNearSemiring n
    rightSemiᵛ = rawRightSemimoduleᵛ rawNearSemiring n
    module LSM = RawLeftSemimodule  leftSemiᵛ
    module RSM = RawRightSemimodule rightSemiᵛ

  open RawMonoidProperties (RawSemiring.*-rawMonoid rawSemiring) n public
    using ()
    renaming (+ᴹ-identity to *ᴹ-identity)

  private
    module ≈  = Definitions NS._≈_
    module LD = LeftDefs  NS.Carrier RNS._≈_
    module RD = RightDefs NS.Carrier RNS._≈_

  *ₗ-identityˡ : ≈.LeftIdentity SR.1# NS._*_ → LD.LeftIdentity SR.1# (λ r xs → LSM._*ₗ_ r xs)
  *ₗ-identityˡ *-idˡ xs i = *-idˡ (xs i)

  *ᵣ-identityʳ : ≈.RightIdentity SR.1# NS._*_ → RD.RightIdentity SR.1# (λ xs r → RSM._*ᵣ_ xs r)
  *ᵣ-identityʳ *-idʳ xs i = *-idʳ (xs i)

------------------------------------------------------------------------

module RawNearSemiringProperties {ℓ ℓr} (R : Semiring ℓ ℓr) (n : ℕ) where
  open Semiring R
  private
    module SR  = RawSemiring rawSemiring
    leftSemiᵛ = rawLeftSemimoduleᵛ rawNearSemiring n
    rightSemiᵛ = rawRightSemimoduleᵛ rawNearSemiring n
    module LSM = RawLeftSemimodule leftSemiᵛ
    nearSemiringᵛ = rawNearSemiringᵛ rawNearSemiring n
    module RNS = RawNearSemiring nearSemiringᵛ
    module RSM = RawRightSemimodule rightSemiᵛ
    module NS = RawNearSemiring rawNearSemiring

  open RawMonoidProperties +-rawMonoid

  isPreleftSemimoduleᵛ : IsPreleftSemimodule R RNS._≈_ RNS._+_ RNS.0# LSM._*ₗ_
  isPreleftSemimoduleᵛ = record
    { *ₗ-cong      = λ x≈y u≈v i     → *-cong x≈y (u≈v i)
    ; *ₗ-zeroˡ     = λ xs i          → zeroˡ (xs i)
    ; *ₗ-distribʳ  = λ xs m n i      → distribʳ (xs i) m n
    ; *ₗ-identityˡ = λ xs i          → *-identityˡ (xs i)
    ; *ₗ-assoc     = λ m n xs i      → *-assoc m n (xs i)
    ; *ₗ-zeroʳ     = λ r i           → zeroʳ r
    ; *ₗ-distribˡ  = λ m xs ys i     → distribˡ m (xs i) (ys i)
    }


  isPrerightSemimoduleᵛ : IsPrerightSemimodule R RNS._≈_ RNS._+_ RNS.0# RSM._*ᵣ_
  isPrerightSemimoduleᵛ = record
    { *ᵣ-cong      = λ x≈y u≈v i     → *-cong (x≈y i) u≈v
    ; *ᵣ-zeroʳ     = λ xs i          → zeroʳ (xs i)
    ; *ᵣ-distribˡ  = λ xs m n i      → distribˡ (xs i) m n
    ; *ᵣ-identityʳ = λ xs i          → *-identityʳ (xs i)
    ; *ᵣ-assoc     = λ xs m n i      → *-assoc (xs i) m n
    ; *ᵣ-zeroˡ     = λ r i           → zeroˡ r
    ; *ᵣ-distribʳ  = λ xs m n i      → distribʳ xs (m i) (n i)
    }

  isBisemimoduleᵛ : IsBisemimodule R R RNS._≈_ RNS._+_ RNS.0# LSM._*ₗ_ RSM._*ᵣ_
  isBisemimoduleᵛ = record
    { +ᴹ-isCommutativeMonoid = isCommutativeMonoidᵛ n +-isCommutativeMonoid
    ; isPreleftSemimodule = isPreleftSemimoduleᵛ
    ; isPrerightSemimodule = isPrerightSemimoduleᵛ
    ; *ₗ-*ᵣ-assoc = λ xs m ys i → *-assoc xs (m i) ys
    }

  private
    module ≈ = Definitions NS._≈_
    module ≈ᴹ = Definitions RNS._≈_

  1#ᵛ : Vector NS.Carrier n
  1#ᵛ = λ _ → SR.1#

  isSemiringᵛ : IsSemiring RNS._≈_ RNS._+_ RNS._*_ RNS.0# 1#ᵛ
  isSemiringᵛ = record
    { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = isCommutativeMonoidᵛ n +-isCommutativeMonoid
        ; *-cong    = λ x≈y u≈v   → ( *-cong   ∘ x≈y) ˢ u≈v
        ; *-assoc   = λ xs ys zs  → ((*-assoc  ∘ xs) ˢ ys) ˢ zs
        ; *-identity = (λ xs → *-identityˡ ∘ xs)
                    , (λ xs → *-identityʳ ∘ xs)
        ; distrib   = (λ xs ys zs → ((distribˡ ∘ xs) ˢ ys) ˢ zs)
                    , (λ xs ys zs → ((distribʳ ∘ xs) ˢ ys) ˢ zs)
        }
    ; zero = (λ xs → zeroˡ ∘ xs) , (λ xs → zeroʳ ∘ xs)
    }

------------------------------------------------------------------------

module MagmaProperties (magma : Magma a ℓ) (n : ℕ) where
  open Magma magma using (_≈_; _∙_; isMagma; rawMagma)
  private
    magmaᵛ = rawMagmaᵛ rawMagma n
    module VM = RawMagma magmaᵛ
    module RM = RawMagma rawMagma

  open RawMagmaProperties rawMagma n public

  +ᴹ-isMagma : IsMagma VM._≈_ VM._∙_
  +ᴹ-isMagma = isMagmaᵛ isMagma

  +ᴹ-magma : Magma _ _
  +ᴹ-magma = record { isMagma = +ᴹ-isMagma }

------------------------------------------------------------------------

module CommutativeMagmaProperties (commutativeMagma : CommutativeMagma a ℓ) (n : ℕ) where
  open CommutativeMagma commutativeMagma
  private
    magmaᵛ = rawMagmaᵛ rawMagma n
    module VM = RawMagma magmaᵛ
    module M  = RawMagma rawMagma

  open MagmaProperties magma n public

  +ᴹ-isCommutativeMagma : IsCommutativeMagma VM._≈_ VM._∙_
  +ᴹ-isCommutativeMagma = isCommutativeMagmaᵛ isCommutativeMagma

  +ᴹ-commutativeMagma : CommutativeMagma _ _
  +ᴹ-commutativeMagma = record { isCommutativeMagma = +ᴹ-isCommutativeMagma }

------------------------------------------------------------------------

module SemiRawGroupProperties (semigroup : Semigroup a ℓ) (n : ℕ) where
  open Semigroup semigroup

  private
    magmaᵛ = rawMagmaᵛ rawMagma n
    module VM = RawMagma magmaᵛ
    module M  = RawMagma rawMagma

  open MagmaProperties magma n public

  +ᴹ-isSemigroup : IsSemigroup VM._≈_ VM._∙_
  +ᴹ-isSemigroup = isSemigroupᵛ isSemigroup

  +ᴹ-semigroup : Semigroup _ _
  +ᴹ-semigroup = record { isSemigroup = +ᴹ-isSemigroup }

------------------------------------------------------------------------

module CommutativeSemigroupProperties (commutativeSemigroup : CommutativeSemigroup a ℓ) (n : ℕ) where
  open CommutativeSemigroup commutativeSemigroup

  private
    magmaᵛ = rawMagmaᵛ rawMagma n
    module VM = RawMagma magmaᵛ
    module M  = RawMagma rawMagma

  open MagmaProperties magma n public

  +ᴹ-isCommutativeSemigroup : IsCommutativeSemigroup VM._≈_ VM._∙_
  +ᴹ-isCommutativeSemigroup = isCommutativeSemigroupᵛ isCommutativeSemigroup

  +ᴹ-commutativeSemigroup : CommutativeSemigroup _ _
  +ᴹ-commutativeSemigroup = record { isCommutativeSemigroup = +ᴹ-isCommutativeSemigroup }

------------------------------------------------------------------------

module MonoidProperties (monoid : Monoid a ℓ) (n : ℕ) where
  open Monoid monoid
  private
    monoidᵛ = rawMonoidᵛ rawMonoid n
    module VM = RawMonoid monoidᵛ
    module M  = RawMonoid rawMonoid

  open RawMonoidProperties rawMonoid n public using (+ᴹ-identity)
  open SemiRawGroupProperties semigroup n public

  +ᴹ-isMonoid : IsMonoid VM._≈_ VM._∙_ VM.ε
  +ᴹ-isMonoid = record
    { isSemigroup = +ᴹ-isSemigroup
    ; identity    = +ᴹ-identity identity
    }

------------------------------------------------------------------------

module CommutativeMonoidProperties (commutativeMonoid : CommutativeMonoid a ℓ) (n : ℕ) where
  open CommutativeMonoid commutativeMonoid

  private
    monoidᵛ = rawMonoidᵛ rawMonoid n
    module VM = RawMonoid monoidᵛ
    module M  = RawMonoid rawMonoid

  open RawMonoidProperties rawMonoid n

  +ᴹ-isCommutativeMonoid : IsCommutativeMonoid VM._≈_ VM._∙_ VM.ε
  +ᴹ-isCommutativeMonoid = isCommutativeMonoidᵛ isCommutativeMonoid

  +ᴹ-commutativeMonoid : CommutativeMonoid _ _
  +ᴹ-commutativeMonoid = record { isCommutativeMonoid = +ᴹ-isCommutativeMonoid }

------------------------------------------------------------------------

module GroupProperties (group : Group a ℓ) (n : ℕ) where
  open Group group

  private
    groupᵛ = rawGroupᵛ rawGroup n
    module VG = RawGroup groupᵛ
    module G  = RawGroup rawGroup

  open RawGroupProperties rawGroup n public using (-ᴹ‿inverse; -ᴹ‿cong)
  open MonoidProperties monoid n public

  +ᴹ-isGroup : IsGroup VG._≈_ VG._∙_ VG.ε VG._⁻¹
  +ᴹ-isGroup = record
    { isMonoid = +ᴹ-isMonoid
    ; inverse  = -ᴹ‿inverse inverse
    ; ⁻¹-cong  = -ᴹ‿cong ⁻¹-cong
    }

  +ᴹ-group : Group _ _
  +ᴹ-group = record { isGroup = +ᴹ-isGroup }

------------------------------------------------------------------------

module AbelianGroupProperties (abelianGroup : AbelianGroup a ℓ) (n : ℕ) where
  open AbelianGroup abelianGroup
  private
    groupᵛ = rawGroupᵛ rawGroup n
    module VG = RawGroup groupᵛ

  open GroupProperties group n public

  +ᴹ-isAbelianGroup : IsAbelianGroup VG._≈_ VG._∙_ VG.ε VG._⁻¹
  +ᴹ-isAbelianGroup = record
    { isGroup = +ᴹ-isGroup
    ; comm    = λ xs ys i → comm (xs i) (ys i)
    }

  +ᴹ-abelianGroup : AbelianGroup _ _
  +ᴹ-abelianGroup = record { isAbelianGroup = +ᴹ-isAbelianGroup }

------------------------------------------------------------------------

module NearSemiringProperties (nearSemiring : NearSemiring a ℓ) (n : ℕ) where
  open NearSemiring nearSemiring
  private
    module N = NearSemiring nearSemiring
    nearSemiringᵛ = rawNearSemiringᵛ rawNearSemiring n
    module RNS = RawNearSemiring nearSemiringᵛ

  open MonoidProperties +-monoid n public using (+ᴹ-isMonoid)

  +ᴹ-*-isNearSemiring : IsNearSemiring RNS._≈_ RNS._+_ RNS._*_ RNS.0#
  +ᴹ-*-isNearSemiring = record
    { +-isMonoid = +ᴹ-isMonoid
    ; *-cong     = λ x≈y u≈v i → N.*-cong (x≈y i) (u≈v i)
    ; *-assoc    = λ xs ys zs i → N.*-assoc (xs i) (ys i) (zs i)
    ; distribʳ   = λ xs ys zs i → N.distribʳ (xs i) (ys i) (zs i)
    ; zeroˡ      = λ xs i → N.zeroˡ (xs i)
    }


  +ᴹ-*-nearSemiring : NearSemiring _ _
  +ᴹ-*-nearSemiring = record { isNearSemiring = +ᴹ-*-isNearSemiring }

------------------------------------------------------------------------

module SemiringWithoutOneProperties (semiringWithoutOne : SemiringWithoutOne a ℓ) (n : ℕ) where
  open SemiringWithoutOne semiringWithoutOne
  private
    nearSemiringᵛ = rawNearSemiringᵛ rawNearSemiring n
    module RNS = RawNearSemiring nearSemiringᵛ
    module SWO = SemiringWithoutOne semiringWithoutOne

  open CommutativeMonoidProperties +-commutativeMonoid n public using (+ᴹ-isCommutativeMonoid)

  +ᴹ-*-isSemiringWithoutOne : IsSemiringWithoutOne RNS._≈_ RNS._+_ RNS._*_ RNS.0#
  +ᴹ-*-isSemiringWithoutOne = record
    { +-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
    ; *-cong                 = λ x≈y u≈v i → SWO.*-cong (x≈y i) (u≈v i)
    ; *-assoc                = λ xs ys zs i → SWO.*-assoc (xs i) (ys i) (zs i)
    ; distrib = (λ xs ys zs i → proj₁ SWO.distrib (xs i) (ys i) (zs i)) ,
                (λ xs ys zs i → proj₂ SWO.distrib (xs i) (ys i) (zs i))
    ; zero    = (λ xs i → proj₁ SWO.zero (xs i)) ,
                (λ xs i → proj₂ SWO.zero (xs i))
    }

  +ᴹ-*-semiringWithoutOne : SemiringWithoutOne _ _
  +ᴹ-*-semiringWithoutOne = record { isSemiringWithoutOne = +ᴹ-*-isSemiringWithoutOne }

------------------------------------------------------------------------

module CommutativeSemiringWithoutOneProperties
  (commutativeSemiringWithoutOne : CommutativeSemiringWithoutOne a ℓ) (n : ℕ) where

  open CommutativeSemiringWithoutOne commutativeSemiringWithoutOne
  private
    module CSWO = CommutativeSemiringWithoutOne commutativeSemiringWithoutOne
    nearSemiringᵛ = rawNearSemiringᵛ rawNearSemiring n
    module RNS = RawNearSemiring nearSemiringᵛ

  open SemiringWithoutOneProperties semiringWithoutOne n public

  +ᴹ-*-isCommutativeSemiringWithoutOne
    : IsCommutativeSemiringWithoutOne RNS._≈_ RNS._+_ RNS._*_ RNS.0#
  +ᴹ-*-isCommutativeSemiringWithoutOne = record
    { isSemiringWithoutOne = +ᴹ-*-isSemiringWithoutOne
    ; *-comm               = λ xs ys i → CSWO.*-comm (xs i) (ys i)
    }

  +ᴹ-*-commutativeSemiringWithoutOne : CommutativeSemiringWithoutOne _ _
  +ᴹ-*-commutativeSemiringWithoutOne =
    record { isCommutativeSemiringWithoutOne = +ᴹ-*-isCommutativeSemiringWithoutOne }

------------------------------------------------------------------------

module SemiringWithoutAnnihilatingZeroProperties
  (semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero a ℓ)
  (n : ℕ) where

  open SemiringWithoutAnnihilatingZero semiringWithoutAnnihilatingZero
  private
    module SWAZ = SemiringWithoutAnnihilatingZero semiringWithoutAnnihilatingZero

    semiringᵛ = rawSemiringᵛ rawSemiring n
    module RS = RawSemiring semiringᵛ

  open VecSemiringProperties rawSemiring n public
  open CommutativeMonoidProperties +-commutativeMonoid n public using (+ᴹ-isCommutativeMonoid)

  +ᴹ-*-isSemiringWithoutAnnihilatingZero
    : IsSemiringWithoutAnnihilatingZero RS._≈_ RS._+_ RS._*_ RS.0# RS.1#
  +ᴹ-*-isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
    ; *-cong    = λ x≈y u≈v i → SWAZ.*-cong (x≈y i) (u≈v i)
    ; *-assoc   = λ xs ys zs i → SWAZ.*-assoc (xs i) (ys i) (zs i)
    ; *-identity = let idˡ , idʳ = SWAZ.*-identity in
        (λ xs i → idˡ (xs i)) , (λ xs i → idʳ (xs i))
    ; distrib = let dˡ , dʳ = SWAZ.distrib in
        (λ xs ys zs i → dˡ (xs i) (ys i) (zs i))
      , (λ xs ys zs i → dʳ (xs i) (ys i) (zs i))
    }

  +ᴹ-*-semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero _ _
  +ᴹ-*-semiringWithoutAnnihilatingZero =
    record { isSemiringWithoutAnnihilatingZero = +ᴹ-*-isSemiringWithoutAnnihilatingZero }

------------------------------------------------------------------------

module SemiringProperties {a ℓ} (semiring : Semiring a ℓ) (n : ℕ) where
  module S = Semiring semiring

  private
    nearSemiringᵛ = rawNearSemiringᵛ S.rawNearSemiring n
    semiringᵛ     = rawSemiringᵛ     S.rawSemiring     n
    module RNS = RawNearSemiring nearSemiringᵛ
    module RS  = RawSemiring     semiringᵛ
    leftSemiᵛ  = rawLeftSemimoduleᵛ  S.rawNearSemiring n
    rightSemiᵛ = rawRightSemimoduleᵛ S.rawNearSemiring n
    module LSM = RawLeftSemimodule  leftSemiᵛ
    module RSM = RawRightSemimodule rightSemiᵛ

    module RN = RawNearSemiringProperties semiring n

  isPreleftSemimodule : IsPreleftSemimodule semiring RNS._≈_ RNS._+_ RNS.0# LSM._*ₗ_
  isPreleftSemimodule = RN.isPreleftSemimoduleᵛ

  isPrerightSemimodule : IsPrerightSemimodule semiring RNS._≈_ RNS._+_ RNS.0# RSM._*ᵣ_
  isPrerightSemimodule = RN.isPrerightSemimoduleᵛ

  isRightSemimodule : IsRightSemimodule semiring RNS._≈_ RNS._+_ RNS.0# RSM._*ᵣ_
  isRightSemimodule = record
    { +ᴹ-isCommutativeMonoid = IsBisemimodule.+ᴹ-isCommutativeMonoid RN.isBisemimoduleᵛ
    ; isPrerightSemimodule   = isPrerightSemimodule
    }

  isBisemimodule : IsBisemimodule semiring semiring RNS._≈_ RNS._+_ RNS.0# LSM._*ₗ_ RSM._*ᵣ_
  isBisemimodule = RN.isBisemimoduleᵛ

  isLeftSemimodule : IsLeftSemimodule semiring RNS._≈_ RNS._+_ RNS.0# LSM._*ₗ_
  isLeftSemimodule = record
    { +ᴹ-isCommutativeMonoid = IsBisemimodule.+ᴹ-isCommutativeMonoid RN.isBisemimoduleᵛ
    ; isPreleftSemimodule    = isPreleftSemimodule
    }

  +ᴹ-*-isSemiring : IsSemiring RS._≈_ RS._+_ RS._*_ RS.0# RS.1#
  +ᴹ-*-isSemiring = RN.isSemiringᵛ

  leftSemimodule : LeftSemimodule _ _ _
  leftSemimodule = record { isLeftSemimodule = isLeftSemimodule }

  +ᴹ-*-semiring : Semiring _ _
  +ᴹ-*-semiring = record { isSemiring = +ᴹ-*-isSemiring }

------------------------------------------------------------------------

module CommutativeSemiringProperties (commutativeSemiring : CommutativeSemiring a ℓ) (n : ℕ) where
  open CommutativeSemiring commutativeSemiring
  private
    module SR = RawSemiring rawSemiring
    baseNearSemiring = SR.rawNearSemiring

    semiringᵛ     = rawSemiringᵛ     rawSemiring     n
    nearSemiringᵛ = rawNearSemiringᵛ baseNearSemiring n
    module RS  = RawSemiring     semiringᵛ
    module RNS = RawNearSemiring nearSemiringᵛ

    module CS = CommutativeSemiring commutativeSemiring

  open SemiringProperties semiring n public

  +ᴹ-*-isCommutativeSemiring : IsCommutativeSemiring RS._≈_ RS._+_ RS._*_ RS.0# RS.1#
  +ᴹ-*-isCommutativeSemiring = record
    { isSemiring = +ᴹ-*-isSemiring
    ; *-comm     = λ xs ys i → CS.*-comm (xs i) (ys i)
    }

  +ᴹ-*-commutativeSemiring : CommutativeSemiring _ _
  +ᴹ-*-commutativeSemiring = record
    { isCommutativeSemiring = +ᴹ-*-isCommutativeSemiring }

------------------------------------------------------------------------

module RingWithoutOneProperties (ringWithoutOne : RingWithoutOne a ℓ) (n : ℕ) where
  open RingWithoutOne ringWithoutOne

  private
    baseNearSemiring : RawNearSemiring a ℓ
    baseNearSemiring = record
      { Carrier = Carrier ; _≈_ = _≈_ ; _+_ = _+_ ; _*_ = _*_ ; 0# = 0# }

    nearSemiringᵛ = rawNearSemiringᵛ baseNearSemiring n
    module RNS = RawNearSemiring nearSemiringᵛ

  private
    module +G = Group +-group
    addRawGroup  = +G.rawGroup
    addGroupᵛ = rawGroupᵛ addRawGroup n
    module VG    = RawGroup addGroupᵛ

  open AbelianGroupProperties +-abelianGroup n using (+ᴹ-isAbelianGroup) public

  private
    module RW1 = IsRingWithoutOne (RingWithoutOne.isRingWithoutOne ringWithoutOne)

  +ᴹ-*-isRingWithoutOne
    : IsRingWithoutOne RNS._≈_ RNS._+_ RNS._*_ VG._⁻¹ RNS.0#
  +ᴹ-*-isRingWithoutOne = record
    { +-isAbelianGroup = +ᴹ-isAbelianGroup
    ; *-cong           = λ x≈y u≈v i → RW1.*-cong (x≈y i) (u≈v i)
    ; *-assoc          = λ xs ys zs i → RW1.*-assoc (xs i) (ys i) (zs i)
    ; distrib          = let dₗ , dᵣ = RW1.distrib in
        (λ xs ys zs i → dₗ (xs i) (ys i) (zs i))
      , (λ xs ys zs i → dᵣ (xs i) (ys i) (zs i))
    }

  +ᴹ-*-ringWithoutOne : RingWithoutOne _ _
  +ᴹ-*-ringWithoutOne = record { isRingWithoutOne = +ᴹ-*-isRingWithoutOne }

------------------------------------------------------------------------

module RingProperties (ring : Ring a ℓ) (n : ℕ) where
  open Ring ring

  private
    module S  = Semiring semiring
    module SR = RawSemiring S.rawSemiring
    baseNearSemiring = SR.rawNearSemiring

    nearSemiringᵛ = rawNearSemiringᵛ baseNearSemiring n
    semiringᵛ     = rawSemiringᵛ     S.rawSemiring    n
    module RNS = RawNearSemiring nearSemiringᵛ
    module RS  = RawSemiring     semiringᵛ

    leftSemiᵛ  = rawLeftSemimoduleᵛ  baseNearSemiring n
    rightSemiᵛ = rawRightSemimoduleᵛ baseNearSemiring n
    module LSM = RawLeftSemimodule  leftSemiᵛ
    module RSM = RawRightSemimodule rightSemiᵛ

    module +G = Group +-group
    addRawGroup = +G.rawGroup
    addGroupᵛ = rawGroupᵛ addRawGroup n
    module VG   = RawGroup addGroupᵛ

  open SemiringProperties semiring n public
  open AbelianGroupProperties +-abelianGroup n public
    using (+ᴹ-isAbelianGroup; -ᴹ‿cong; -ᴹ‿inverse)

  isRightModule : IsRightModule ring RNS._≈_ RNS._+_ RNS.0# VG._⁻¹ RSM._*ᵣ_
  isRightModule = record
    { isRightSemimodule = isRightSemimodule
    ; -ᴹ‿cong           = -ᴹ‿cong -‿cong
    ; -ᴹ‿inverse        = -ᴹ‿inverse -‿inverse
    }

  isBimodule : IsBimodule ring ring RNS._≈_ RNS._+_ RNS.0# VG._⁻¹ LSM._*ₗ_ RSM._*ᵣ_
  isBimodule = record
    { isBisemimodule = isBisemimodule
    ; -ᴹ‿cong        = -ᴹ‿cong -‿cong
    ; -ᴹ‿inverse     = -ᴹ‿inverse -‿inverse
    }

  isLeftModule : IsLeftModule ring RNS._≈_ RNS._+_ RNS.0# VG._⁻¹ LSM._*ₗ_
  isLeftModule = record
    { isLeftSemimodule = isLeftSemimodule
    ; -ᴹ‿cong          = -ᴹ‿cong -‿cong
    ; -ᴹ‿inverse       = -ᴹ‿inverse -‿inverse
    }

  +ᴹ-*-isRing : IsRing RS._≈_ RS._+_ RS._*_ VG._⁻¹ RS.0# RS.1#
  +ᴹ-*-isRing = record
    { +-isAbelianGroup = +ᴹ-isAbelianGroup
    ; *-cong           = λ x≈y u≈v i → *-cong (x≈y i) (u≈v i)
    ; *-assoc          = λ xs ys zs i → *-assoc (xs i) (ys i) (zs i)
    ; *-identity       = let idₗ , idᵣ = *-identity in
        (λ xs i → idₗ (xs i)) , (λ xs i → idᵣ (xs i))
    ; distrib          = let dₗ , dᵣ = distrib in
        (λ xs ys zs i → dₗ (xs i) (ys i) (zs i))
      , (λ xs ys zs i → dᵣ (xs i) (ys i) (zs i))
    }

  leftModule : LeftModule _ _ _
  leftModule = record { isLeftModule = isLeftModule }

  bisemimodule : Bisemimodule _ _ _ _
  bisemimodule = record { isBisemimodule = isBisemimodule }

  rightModule : RightModule _ _ _
  rightModule = record { isRightModule = isRightModule }

  bimodule : Bimodule _ _ _ _
  bimodule = record { isBimodule = isBimodule }

------------------------------------------------------------------------

module CommutativeRingProperties (commutativeRing : CommutativeRing a ℓ) (n : ℕ) where
  open CommutativeRing commutativeRing
  private
    module Ri = Ring ring
    module S  = Semiring Ri.semiring
    module SR = RawSemiring S.rawSemiring
    baseNearSemiring = SR.rawNearSemiring

    nearSemiringᵛ = rawNearSemiringᵛ baseNearSemiring n
    semiringᵛ     = rawSemiringᵛ     S.rawSemiring    n

    module RNS = RawNearSemiring nearSemiringᵛ
    module RS  = RawSemiring     semiringᵛ

    leftSemiᵛ  = rawLeftSemimoduleᵛ  baseNearSemiring n
    rightSemiᵛ = rawRightSemimoduleᵛ baseNearSemiring n
    module LSM = RawLeftSemimodule  leftSemiᵛ
    module RSM = RawRightSemimodule rightSemiᵛ

    module +G = Group Ri.+-group
    addRawGroup = +G.rawGroup
    addGroupᵛ = rawGroupᵛ addRawGroup n
    module VG   = RawGroup addGroupᵛ

  open RingProperties ring n public

  +ᴹ-*-isCommutativeRing
    : IsCommutativeRing RS._≈_ RS._+_ RS._*_ VG._⁻¹ RS.0# RS.1#
  +ᴹ-*-isCommutativeRing = record
    { isRing = +ᴹ-*-isRing
    ; *-comm = λ xs ys i → *-comm (xs i) (ys i)
    }

  isModule : IsModule commutativeRing RNS._≈_ RNS._+_ RNS.0# VG._⁻¹ LSM._*ₗ_ RSM._*ᵣ_
  isModule = record
    { isBimodule = isBimodule
    ; *ₗ-*ᵣ-coincident = λ r xs i → *-comm r (xs i)
    }

  module' : Module _ _ _
  module' = record { isModule = isModule }