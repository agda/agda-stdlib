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
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as Pointwise
import Data.Vec.Functional.Algebra.Base as V

private variable
  a ℓ : Level
  A : Set ℓ
  n : ℕ

------------------------------------------------------------------------
-- Raw structure properties

module RawMagmaProperties (M : RawMagma a ℓ) (n : ℕ) where
  module VM = RawMagma (V.rawMagma M n)
  module M  = RawMagma M

  isMagma : IsMagma M._≈_ M._∙_ → IsMagma VM._≈_ VM._∙_
  isMagma base = record
    { isEquivalence = flip Pointwise.isEquivalence _ B.isEquivalence
    ; ∙-cong        = λ x≈y u≈v i → B.∙-cong (x≈y i) (u≈v i)
    }
    where module B = IsMagma base

  isCommutativeMagma :
    IsCommutativeMagma M._≈_ M._∙_ →
    IsCommutativeMagma VM._≈_ VM._∙_
  isCommutativeMagma base = record
    { isMagma = isMagma B.isMagma
    ; comm    = λ xs ys i → B.comm (xs i) (ys i)
    }
    where module B = IsCommutativeMagma base

  isSemigroup :
    IsSemigroup M._≈_ M._∙_ →
    IsSemigroup VM._≈_ VM._∙_
  isSemigroup base = record
    { isMagma = isMagma B.isMagma
    ; assoc   = λ xs ys zs i → B.assoc (xs i) (ys i) (zs i)
    }
    where module B = IsSemigroup base

  isCommutativeSemigroup :
    IsCommutativeSemigroup M._≈_ M._∙_ →
    IsCommutativeSemigroup VM._≈_ VM._∙_
  isCommutativeSemigroup base = record
    { isSemigroup = isSemigroup B.isSemigroup
    ; comm        = λ xs ys i → B.comm (xs i) (ys i)
    }
    where module B = IsCommutativeSemigroup base

------------------------------------------------------------------------

module RawMonoidProperties (RM : RawMonoid a ℓ) (n : ℕ) where
  module VMon = RawMonoid (V.rawMonoid RM n)
  module RM  = RawMonoid RM

  open RawMagmaProperties RM.rawMagma n public

  private
    module ≈  = Definitions RM._≈_
    module ≈ᴹ = Definitions VMon._≈_

  +ᴹ-identityˡ : ≈.LeftIdentity RM.ε RM._∙_ → ≈ᴹ.LeftIdentity VMon.ε VMon._∙_
  +ᴹ-identityˡ idˡ xs i = idˡ (xs i)

  +ᴹ-identityʳ : ≈.RightIdentity RM.ε RM._∙_ → ≈ᴹ.RightIdentity VMon.ε VMon._∙_
  +ᴹ-identityʳ idʳ xs i = idʳ (xs i)

  +ᴹ-identity : ≈.Identity RM.ε RM._∙_ → ≈ᴹ.Identity VMon.ε VMon._∙_
  +ᴹ-identity (idˡ , idʳ) = +ᴹ-identityˡ idˡ , +ᴹ-identityʳ idʳ

  isMonoidᵛ : IsMonoid RM._≈_ RM._∙_ RM.ε → IsMonoid VMon._≈_ VMon._∙_ VMon.ε
  isMonoidᵛ isMonoid = record
    { isSemigroup = isSemigroup Mon.isSemigroup
    ; identity    = +ᴹ-identity Mon.identity
    } where module Mon = IsMonoid isMonoid

  isCommutativeMonoidᵛ :
    IsCommutativeMonoid RM._≈_ RM._∙_ RM.ε →
    IsCommutativeMonoid VMon._≈_ VMon._∙_ VMon.ε
  isCommutativeMonoidᵛ base = record
    { isMonoid = isMonoidᵛ CM.isMonoid
    ; comm     = λ xs ys i → CM.comm (xs i) (ys i)
    } where module CM = IsCommutativeMonoid base

------------------------------------------------------------------------

module RawGroupProperties (RG : RawGroup a ℓ) (n : ℕ) where
  private
    module VGp = RawGroup (V.rawGroup RG n)
    module G   = RawGroup RG

  open RawMonoidProperties G.rawMonoid n public

  private
    module ≈ = Definitions G._≈_
    module ≈ᴹ = Definitions VGp._≈_

  -ᴹ‿inverseˡ : ≈.LeftInverse G.ε G._⁻¹ G._∙_ → ≈ᴹ.LeftInverse VGp.ε VGp._⁻¹ VGp._∙_
  -ᴹ‿inverseˡ -‿inverseˡ xs i = -‿inverseˡ (xs i)

  -ᴹ‿inverseʳ : ≈.RightInverse G.ε G._⁻¹ G._∙_ → ≈ᴹ.RightInverse VGp.ε VGp._⁻¹ VGp._∙_
  -ᴹ‿inverseʳ -‿inverseʳ xs i = -‿inverseʳ (xs i)

  -ᴹ‿inverse : ≈.Inverse G.ε G._⁻¹ G._∙_ → ≈ᴹ.Inverse VGp.ε VGp._⁻¹ VGp._∙_
  -ᴹ‿inverse (-‿inverseˡ , -‿inverseʳ) = -ᴹ‿inverseˡ -‿inverseˡ , -ᴹ‿inverseʳ -‿inverseʳ

  -ᴹ‿cong : ≈.Congruent₁ G._⁻¹ → ≈ᴹ.Congruent₁ VGp._⁻¹
  -ᴹ‿cong -‿cong xs≈ys i = -‿cong (xs≈ys i)

  isGroupᵛ : IsGroup G._≈_ G._∙_ G.ε G._⁻¹ → IsGroup VGp._≈_ VGp._∙_ VGp.ε VGp._⁻¹
  isGroupᵛ isGroup = record
    { isMonoid = isMonoidᵛ Gr.isMonoid
    ; inverse = -ᴹ‿inverse Gr.inverse
    ; ⁻¹-cong = -ᴹ‿cong Gr.⁻¹-cong
    } where module Gr = IsGroup isGroup

  isAbelianGroupᵛ : IsAbelianGroup G._≈_ G._∙_ G.ε G._⁻¹ → IsAbelianGroup VGp._≈_ VGp._∙_ VGp.ε VGp._⁻¹
  isAbelianGroupᵛ base = record
    { isGroup = isGroupᵛ AG.isGroup
    ; comm    = λ xs ys i → AG.comm (xs i) (ys i)
    }
    where module AG = IsAbelianGroup base

------------------------------------------------------------------------

module VecSemiringProperties (rawSemiring : RawSemiring a ℓ) (n : ℕ) where
  private
    module SR  = RawSemiring rawSemiring
    RNS = SR.rawNearSemiring
    module NS  = RawNearSemiring RNS
    nearSemiringᵛ = V.rawNearSemiring RNS n
    module RNS = RawNearSemiring nearSemiringᵛ
    leftSemiᵛ  = V.rawLeftSemimodule  RNS n
    rightSemiᵛ = V.rawRightSemimodule RNS n
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
  module S = Semiring R
  private
    module SR = RawSemiring     S.rawSemiring
    module NS = RawNearSemiring S.rawNearSemiring

    leftSemiᵛ   = V.rawLeftSemimodule  S.rawNearSemiring n
    rightSemiᵛ  = V.rawRightSemimodule S.rawNearSemiring n
    nearSemiringᵛ = V.rawNearSemiring  S.rawNearSemiring n

    module LSM = RawLeftSemimodule  leftSemiᵛ
    module RSM = RawRightSemimodule rightSemiᵛ
    module RNS = RawNearSemiring    nearSemiringᵛ

  open RawMonoidProperties S.+-rawMonoid n

  isPreleftSemimoduleᵛ : IsPreleftSemimodule R RNS._≈_ RNS._+_ RNS.0# LSM._*ₗ_
  isPreleftSemimoduleᵛ = record
    { *ₗ-cong      = λ x≈y u≈v i     → S.*-cong x≈y (u≈v i)
    ; *ₗ-zeroˡ     = λ xs i          → S.zeroˡ (xs i)
    ; *ₗ-distribʳ  = λ xs m n i      → S.distribʳ (xs i) m n
    ; *ₗ-identityˡ = λ xs i          → S.*-identityˡ (xs i)
    ; *ₗ-assoc     = λ m n xs i      → S.*-assoc m n (xs i)
    ; *ₗ-zeroʳ     = λ r i           → S.zeroʳ r
    ; *ₗ-distribˡ  = λ m xs ys i     → S.distribˡ m (xs i) (ys i)
    }


  isPrerightSemimoduleᵛ : IsPrerightSemimodule R RNS._≈_ RNS._+_ RNS.0# RSM._*ᵣ_
  isPrerightSemimoduleᵛ = record
    { *ᵣ-cong      = λ x≈y u≈v i     → S.*-cong (x≈y i) u≈v
    ; *ᵣ-zeroʳ     = λ xs i          → S.zeroʳ (xs i)
    ; *ᵣ-distribˡ  = λ xs m n i      → S.distribˡ (xs i) m n
    ; *ᵣ-identityʳ = λ xs i          → S.*-identityʳ (xs i)
    ; *ᵣ-assoc     = λ xs m n i      → S.*-assoc (xs i) m n
    ; *ᵣ-zeroˡ     = λ r i           → S.zeroˡ r
    ; *ᵣ-distribʳ  = λ xs m n i      → S.distribʳ xs (m i) (n i)
    }

  isBisemimoduleᵛ : IsBisemimodule R R RNS._≈_ RNS._+_ RNS.0# LSM._*ₗ_ RSM._*ᵣ_
  isBisemimoduleᵛ = record
    { +ᴹ-isCommutativeMonoid = isCommutativeMonoidᵛ S.+-isCommutativeMonoid
    ; isPreleftSemimodule = isPreleftSemimoduleᵛ
    ; isPrerightSemimodule = isPrerightSemimoduleᵛ
    ; *ₗ-*ᵣ-assoc = λ xs m ys i → S.*-assoc xs (m i) ys
    }

  private
    module ≈ = Definitions NS._≈_
    module ≈ᴹ = Definitions RNS._≈_

  1#ᵛ : Vector NS.Carrier n
  1#ᵛ = λ _ → SR.1#

  isSemiringᵛ : IsSemiring RNS._≈_ RNS._+_ RNS._*_ RNS.0# 1#ᵛ
  isSemiringᵛ = record
    { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = isCommutativeMonoidᵛ S.+-isCommutativeMonoid
        ; *-cong    = λ x≈y u≈v   → ( S.*-cong   ∘ x≈y) ˢ u≈v
        ; *-assoc   = λ xs ys zs  → ((S.*-assoc  ∘ xs) ˢ ys) ˢ zs
        ; *-identity = (λ xs → S.*-identityˡ ∘ xs)
                    , (λ xs → S.*-identityʳ ∘ xs)
        ; distrib   = (λ xs ys zs → ((S.distribˡ ∘ xs) ˢ ys) ˢ zs)
                    , (λ xs ys zs → ((S.distribʳ ∘ xs) ˢ ys) ˢ zs)
        }
    ; zero = (λ xs → S.zeroˡ ∘ xs) , (λ xs → S.zeroʳ ∘ xs)
    }

------------------------------------------------------------------------

module MagmaProperties (magma : Magma a ℓ) (n : ℕ) where
  module Mg = Magma magma
  module VM = RawMagma (V.rawMagma Mg.rawMagma n)
  module RM = RawMagma Mg.rawMagma

  open RawMagmaProperties Mg.rawMagma n public
    renaming (isMagma to isMagmaᵛ)
    hiding (module M; module VM)

  +ᴹ-isMagma : IsMagma VM._≈_ VM._∙_
  +ᴹ-isMagma = isMagmaᵛ Mg.isMagma

  +ᴹ-magma : Magma _ _
  +ᴹ-magma = record { isMagma = +ᴹ-isMagma }

------------------------------------------------------------------------

module CommutativeMagmaProperties (cMag : CommutativeMagma a ℓ) (n : ℕ) where
  module CM = CommutativeMagma cMag
  module VM = RawMagma (V.rawMagma CM.rawMagma n)
  module B  = RawMagma CM.rawMagma

  open MagmaProperties CM.magma n public
    renaming (isCommutativeMagma to isCommutativeMagmaᵛ)
    hiding (module VM; module RM)

  +ᴹ-isCommutativeMagma : IsCommutativeMagma VM._≈_ VM._∙_
  +ᴹ-isCommutativeMagma = isCommutativeMagmaᵛ CM.isCommutativeMagma

  +ᴹ-commutativeMagma : CommutativeMagma _ _
  +ᴹ-commutativeMagma = record { isCommutativeMagma = +ᴹ-isCommutativeMagma }

------------------------------------------------------------------------

module SemiRawGroupProperties (sg : Semigroup a ℓ) (n : ℕ) where
  module SG = Semigroup sg
  module VM = RawMagma (V.rawMagma SG.rawMagma n)
  module B  = RawMagma SG.rawMagma

  open MagmaProperties SG.magma n public
    renaming (isSemigroup to isSemigroupᵛ)
    hiding (module VM; module RM)

  +ᴹ-isSemigroup : IsSemigroup VM._≈_ VM._∙_
  +ᴹ-isSemigroup = isSemigroupᵛ SG.isSemigroup

  +ᴹ-semigroup : Semigroup _ _
  +ᴹ-semigroup = record { isSemigroup = +ᴹ-isSemigroup }

------------------------------------------------------------------------

module CommutativeSemigroupProperties (csg : CommutativeSemigroup a ℓ) (n : ℕ) where
  module CS = CommutativeSemigroup csg
  module VM = RawMagma (V.rawMagma CS.rawMagma n)
  module B  = RawMagma CS.rawMagma

  open MagmaProperties CS.magma n public
    renaming (isCommutativeSemigroup to isCommutativeSemigroupᵛ)
    hiding (module VM; module RM)

  +ᴹ-isCommutativeSemigroup : IsCommutativeSemigroup VM._≈_ VM._∙_
  +ᴹ-isCommutativeSemigroup = isCommutativeSemigroupᵛ CS.isCommutativeSemigroup

  +ᴹ-commutativeSemigroup : CommutativeSemigroup _ _
  +ᴹ-commutativeSemigroup = record { isCommutativeSemigroup = +ᴹ-isCommutativeSemigroup }

------------------------------------------------------------------------

module MonoidProperties (mon : Monoid a ℓ) (n : ℕ) where
  module M = Monoid mon
  module VMon    = RawMonoid (V.rawMonoid M.rawMonoid n)
  module BaseMon = RawMonoid M.rawMonoid

  open RawMonoidProperties M.rawMonoid n public using (+ᴹ-identity)
  open SemiRawGroupProperties M.semigroup n public hiding (module B)

  +ᴹ-isMonoid : IsMonoid VMon._≈_ VMon._∙_ VMon.ε
  +ᴹ-isMonoid = record
    { isSemigroup = +ᴹ-isSemigroup
    ; identity    = +ᴹ-identity M.identity
    }


------------------------------------------------------------------------

module CommutativeMonoidProperties (cMon : CommutativeMonoid a ℓ) (n : ℕ) where
  module CM = CommutativeMonoid cMon
  module VMonL    = RawMonoid (V.rawMonoid CM.rawMonoid n)
  module BaseMon  = RawMonoid CM.rawMonoid

  open RawMonoidProperties CM.rawMonoid n public

  +ᴹ-isCommutativeMonoid : IsCommutativeMonoid VMonL._≈_ VMonL._∙_ VMonL.ε
  +ᴹ-isCommutativeMonoid = isCommutativeMonoidᵛ CM.isCommutativeMonoid

  +ᴹ-commutativeMonoid : CommutativeMonoid _ _
  +ᴹ-commutativeMonoid = record { isCommutativeMonoid = +ᴹ-isCommutativeMonoid }


------------------------------------------------------------------------

module GroupProperties (grp : Group a ℓ) (n : ℕ) where
  module G = Group grp
  module VGrp  = RawGroup (V.rawGroup G.rawGroup n)
  module BaseG = RawGroup G.rawGroup

  open RawGroupProperties G.rawGroup n public using (-ᴹ‿inverse; -ᴹ‿cong)
  open MonoidProperties G.monoid n public

  +ᴹ-isGroup : IsGroup VGrp._≈_ VGrp._∙_ VGrp.ε VGrp._⁻¹
  +ᴹ-isGroup = record
    { isMonoid = +ᴹ-isMonoid
    ; inverse  = -ᴹ‿inverse G.inverse
    ; ⁻¹-cong  = -ᴹ‿cong   G.⁻¹-cong
    }

  +ᴹ-group : Group _ _
  +ᴹ-group = record { isGroup = +ᴹ-isGroup }

------------------------------------------------------------------------

module AbelianGroupProperties (abg : AbelianGroup a ℓ) (n : ℕ) where
  module AG = AbelianGroup abg
  module VGroupL = RawGroup (V.rawGroup AG.rawGroup n)

  open GroupProperties AG.group n public

  +ᴹ-isAbelianGroup : IsAbelianGroup VGroupL._≈_ VGroupL._∙_ VGroupL.ε VGroupL._⁻¹
  +ᴹ-isAbelianGroup = record
    { isGroup = +ᴹ-isGroup
    ; comm    = λ xs ys i → AG.comm (xs i) (ys i)
    }

  +ᴹ-abelianGroup : AbelianGroup _ _
  +ᴹ-abelianGroup = record { isAbelianGroup = +ᴹ-isAbelianGroup }

------------------------------------------------------------------------

module NearSemiringProperties (near : NearSemiring a ℓ) (n : ℕ) where
  module NS = NearSemiring near

  NSᵛ : RawNearSemiring a ℓ
  NSᵛ = V.rawNearSemiring NS.rawNearSemiring n
  module RNS = RawNearSemiring NSᵛ

  open MonoidProperties NS.+-monoid n public using (+ᴹ-isMonoid)

  +ᴹ-*-isNearSemiring : IsNearSemiring RNS._≈_ RNS._+_ RNS._*_ RNS.0#
  +ᴹ-*-isNearSemiring = record
    { +-isMonoid = +ᴹ-isMonoid
    ; *-cong     = λ x≈y u≈v i → NS.*-cong (x≈y i) (u≈v i)
    ; *-assoc    = λ xs ys zs i → NS.*-assoc (xs i) (ys i) (zs i)
    ; distribʳ   = λ xs ys zs i → NS.distribʳ (xs i) (ys i) (zs i)
    ; zeroˡ      = λ xs i       → NS.zeroˡ (xs i)
    }

  +ᴹ-*-nearSemiring : NearSemiring _ _
  +ᴹ-*-nearSemiring = record { isNearSemiring = +ᴹ-*-isNearSemiring }

------------------------------------------------------------------------

module SemiringWithoutOneProperties (swo : SemiringWithoutOne a ℓ) (n : ℕ) where
  module SWO = SemiringWithoutOne swo
  module RNS = RawNearSemiring (V.rawNearSemiring SWO.rawNearSemiring n)

  open CommutativeMonoidProperties SWO.+-commutativeMonoid n public
    using (+ᴹ-isCommutativeMonoid)

  +ᴹ-*-isSemiringWithoutOne :
    IsSemiringWithoutOne RNS._≈_ RNS._+_ RNS._*_ RNS.0#
  +ᴹ-*-isSemiringWithoutOne = record
    { +-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
    ; *-cong   = λ x≈y u≈v i → SWO.*-cong (x≈y i) (u≈v i)
    ; *-assoc  = λ xs ys zs i → SWO.*-assoc (xs i) (ys i) (zs i)
    ; distrib  =
        (λ xs ys zs i → proj₁ SWO.distrib (xs i) (ys i) (zs i)) ,
        (λ xs ys zs i → proj₂ SWO.distrib (xs i) (ys i) (zs i))
    ; zero     =
        (λ xs i → proj₁ SWO.zero (xs i)) ,
        (λ xs i → proj₂ SWO.zero (xs i))
    }

  +ᴹ-*-semiringWithoutOne : SemiringWithoutOne _ _
  +ᴹ-*-semiringWithoutOne = record
    { isSemiringWithoutOne = +ᴹ-*-isSemiringWithoutOne }

------------------------------------------------------------------------

module CommutativeSemiringWithoutOneProperties
  (cswo : CommutativeSemiringWithoutOne a ℓ) (n : ℕ) where

  module CSWO = CommutativeSemiringWithoutOne cswo
  module VNS = RawNearSemiring (V.rawNearSemiring CSWO.rawNearSemiring n)

  open SemiringWithoutOneProperties CSWO.semiringWithoutOne n public

  +ᴹ-*-isCommutativeSemiringWithoutOne :
    IsCommutativeSemiringWithoutOne VNS._≈_ VNS._+_ VNS._*_ VNS.0#
  +ᴹ-*-isCommutativeSemiringWithoutOne = record
    { isSemiringWithoutOne = +ᴹ-*-isSemiringWithoutOne
    ; *-comm               = λ xs ys i → CSWO.*-comm (xs i) (ys i)
    }

  +ᴹ-*-commutativeSemiringWithoutOne : CommutativeSemiringWithoutOne _ _
  +ᴹ-*-commutativeSemiringWithoutOne =
    record { isCommutativeSemiringWithoutOne = +ᴹ-*-isCommutativeSemiringWithoutOne }

------------------------------------------------------------------------

module SemiringWithoutAnnihilatingZeroProperties
  (swaz : SemiringWithoutAnnihilatingZero a ℓ)
  (n : ℕ) where

  module SWAZ = SemiringWithoutAnnihilatingZero swaz
  module RSv = RawSemiring (V.rawSemiring SWAZ.rawSemiring n)

  open VecSemiringProperties SWAZ.rawSemiring n public
  open CommutativeMonoidProperties SWAZ.+-commutativeMonoid n public
    using (+ᴹ-isCommutativeMonoid)

  +ᴹ-*-isSemiringWithoutAnnihilatingZero
    : IsSemiringWithoutAnnihilatingZero RSv._≈_ RSv._+_ RSv._*_ RSv.0# RSv.1#
  +ᴹ-*-isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
    ; *-cong    = λ x≈y u≈v i → SWAZ.*-cong (x≈y i) (u≈v i)
    ; *-assoc   = λ xs ys zs i → SWAZ.*-assoc (xs i) (ys i) (zs i)
    ; *-identity = let idˡ , idʳ = SWAZ.*-identity in
        (λ xs i → idˡ (xs i)) , (λ xs i → idʳ (xs i))
    ; distrib   = let dˡ , dʳ = SWAZ.distrib in
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
    module RNS = RawNearSemiring (V.rawNearSemiring S.rawNearSemiring n)
    module RS  = RawSemiring     (V.rawSemiring     S.rawSemiring     n)
    module LSM = RawLeftSemimodule  (V.rawLeftSemimodule  S.rawNearSemiring n)
    module RSM = RawRightSemimodule (V.rawRightSemimodule S.rawNearSemiring n)

    module RN  = RawNearSemiringProperties semiring n

  isPreleftSemimodule :
    IsPreleftSemimodule semiring RNS._≈_ RNS._+_ RNS.0# LSM._*ₗ_
  isPreleftSemimodule = RN.isPreleftSemimoduleᵛ

  isPrerightSemimodule :
    IsPrerightSemimodule semiring RNS._≈_ RNS._+_ RNS.0# RSM._*ᵣ_
  isPrerightSemimodule = RN.isPrerightSemimoduleᵛ

  isRightSemimodule :
    IsRightSemimodule semiring RNS._≈_ RNS._+_ RNS.0# RSM._*ᵣ_
  isRightSemimodule = record
    { +ᴹ-isCommutativeMonoid =
        IsBisemimodule.+ᴹ-isCommutativeMonoid RN.isBisemimoduleᵛ
    ; isPrerightSemimodule   = isPrerightSemimodule
    }

  isBisemimodule :
    IsBisemimodule semiring semiring RNS._≈_ RNS._+_ RNS.0# LSM._*ₗ_ RSM._*ᵣ_
  isBisemimodule = RN.isBisemimoduleᵛ

  isLeftSemimodule :
    IsLeftSemimodule semiring RNS._≈_ RNS._+_ RNS.0# LSM._*ₗ_
  isLeftSemimodule = record
    { +ᴹ-isCommutativeMonoid =
        IsBisemimodule.+ᴹ-isCommutativeMonoid RN.isBisemimoduleᵛ
    ; isPreleftSemimodule    = isPreleftSemimodule
    }

  +ᴹ-*-isSemiring : IsSemiring RS._≈_ RS._+_ RS._*_ RS.0# RS.1#
  +ᴹ-*-isSemiring = RN.isSemiringᵛ

  leftSemimodule : LeftSemimodule _ _ _
  leftSemimodule = record { isLeftSemimodule = isLeftSemimodule }

  +ᴹ-*-semiring : Semiring _ _
  +ᴹ-*-semiring = record { isSemiring = +ᴹ-*-isSemiring }


------------------------------------------------------------------------

module CommutativeSemiringProperties
  (cSem : CommutativeSemiring a ℓ) (n : ℕ) where

  module CS = CommutativeSemiring cSem
  module RSv = RawSemiring (V.rawSemiring CS.rawSemiring n)

  open SemiringProperties CS.semiring n public

  +ᴹ-*-isCommutativeSemiring :
    IsCommutativeSemiring RSv._≈_ RSv._+_ RSv._*_ RSv.0# RSv.1#
  +ᴹ-*-isCommutativeSemiring = record
    { isSemiring = +ᴹ-*-isSemiring
    ; *-comm     = λ xs ys i → CS.*-comm (xs i) (ys i)
    }

  +ᴹ-*-commutativeSemiring : CommutativeSemiring _ _
  +ᴹ-*-commutativeSemiring =
    record { isCommutativeSemiring = +ᴹ-*-isCommutativeSemiring }

------------------------------------------------------------------------

module RingWithoutOneProperties (rwo : RingWithoutOne a ℓ) (n : ℕ) where
  module RW = RingWithoutOne rwo

  private
    baseNearSemiring : RawNearSemiring a ℓ
    baseNearSemiring = record
      { Carrier = RW.Carrier
      ; _≈_     = RW._≈_
      ; _+_     = RW._+_
      ; _*_     = RW._*_
      ; 0#      = RW.0#
      }

    module RNS = RawNearSemiring (V.rawNearSemiring baseNearSemiring n)

  private
    module +G  = Group RW.+-group
    addRawGroup = +G.rawGroup
    module VG  = RawGroup (V.rawGroup addRawGroup n)

  open AbelianGroupProperties RW.+-abelianGroup n using (+ᴹ-isAbelianGroup) public

  private
    module IW1 = IsRingWithoutOne RW.isRingWithoutOne

  +ᴹ-*-isRingWithoutOne :
    IsRingWithoutOne RNS._≈_ RNS._+_ RNS._*_ VG._⁻¹ RNS.0#
  +ᴹ-*-isRingWithoutOne = record
    { +-isAbelianGroup = +ᴹ-isAbelianGroup
    ; *-cong           = λ x≈y u≈v i → IW1.*-cong (x≈y i) (u≈v i)
    ; *-assoc          = λ xs ys zs i → IW1.*-assoc (xs i) (ys i) (zs i)
    ; distrib          = let dₗ , dᵣ = IW1.distrib in
        (λ xs ys zs i → dₗ (xs i) (ys i) (zs i))
      , (λ xs ys zs i → dᵣ (xs i) (ys i) (zs i))
    }

  +ᴹ-*-ringWithoutOne : RingWithoutOne _ _
  +ᴹ-*-ringWithoutOne = record { isRingWithoutOne = +ᴹ-*-isRingWithoutOne }

------------------------------------------------------------------------

module RingProperties (ring : Ring a ℓ) (n : ℕ) where
  module Rg = Ring ring
  private
    module S    = Semiring Rg.semiring
    module RNSv = RawNearSemiring (V.rawNearSemiring S.rawNearSemiring n)
    module RSv  = RawSemiring     (V.rawSemiring     S.rawSemiring     n)
    module LSMv = RawLeftSemimodule  (V.rawLeftSemimodule  S.rawNearSemiring n)
    module RSMv = RawRightSemimodule (V.rawRightSemimodule S.rawNearSemiring n)
    module +G   = Group Rg.+-group
    module VGrp = RawGroup (V.rawGroup +G.rawGroup n)

  open SemiringProperties Rg.semiring n public
  open AbelianGroupProperties Rg.+-abelianGroup n public
    using (+ᴹ-isAbelianGroup; -ᴹ‿cong; -ᴹ‿inverse)

  isRightModule :
    IsRightModule ring RNSv._≈_ RNSv._+_ RNSv.0# VGrp._⁻¹ RSMv._*ᵣ_
  isRightModule = record
    { isRightSemimodule = isRightSemimodule
    ; -ᴹ‿cong           = -ᴹ‿cong Rg.-‿cong
    ; -ᴹ‿inverse        = -ᴹ‿inverse Rg.-‿inverse
    }

  isBimodule :
    IsBimodule ring ring RNSv._≈_ RNSv._+_ RNSv.0# VGrp._⁻¹ LSMv._*ₗ_ RSMv._*ᵣ_
  isBimodule = record
    { isBisemimodule = isBisemimodule
    ; -ᴹ‿cong        = -ᴹ‿cong Rg.-‿cong
    ; -ᴹ‿inverse     = -ᴹ‿inverse Rg.-‿inverse
    }

  isLeftModule :
    IsLeftModule ring RNSv._≈_ RNSv._+_ RNSv.0# VGrp._⁻¹ LSMv._*ₗ_
  isLeftModule = record
    { isLeftSemimodule = isLeftSemimodule
    ; -ᴹ‿cong          = -ᴹ‿cong Rg.-‿cong
    ; -ᴹ‿inverse       = -ᴹ‿inverse Rg.-‿inverse
    }

  +ᴹ-*-isRing : IsRing RSv._≈_ RSv._+_ RSv._*_ VGrp._⁻¹ RSv.0# RSv.1#
  +ᴹ-*-isRing = record
    { +-isAbelianGroup = +ᴹ-isAbelianGroup
    ; *-cong           = λ x≈y u≈v i → Rg.*-cong (x≈y i) (u≈v i)
    ; *-assoc          = λ xs ys zs i → Rg.*-assoc (xs i) (ys i) (zs i)
    ; *-identity       =
        let idₗ , idᵣ = Rg.*-identity in
          (λ xs i → idₗ (xs i)) , (λ xs i → idᵣ (xs i))
    ; distrib          =
        let dₗ , dᵣ = Rg.distrib in
          (λ xs ys zs i → dₗ (xs i) (ys i) (zs i)) ,
          (λ xs ys zs i → dᵣ (xs i) (ys i) (zs i))
    }

  leftModule  : LeftModule  _ _ _
  leftModule  = record { isLeftModule  = isLeftModule }

  bisemimodule : Bisemimodule _ _ _ _
  bisemimodule = record { isBisemimodule = isBisemimodule }

  rightModule : RightModule _ _ _
  rightModule = record { isRightModule = isRightModule }

  bimodule    : Bimodule _ _ _ _
  bimodule    = record { isBimodule    = isBimodule }

------------------------------------------------------------------------

module CommutativeRingProperties (cRing : CommutativeRing a ℓ) (n : ℕ) where
  module CR = CommutativeRing cRing

  module Ri  = Ring CR.ring
  module Sem = Semiring Ri.semiring

  module RNSv = RawNearSemiring (V.rawNearSemiring Sem.rawNearSemiring n)
  module RSv  = RawSemiring     (V.rawSemiring     Sem.rawSemiring     n)
  module LSMv = RawLeftSemimodule  (V.rawLeftSemimodule  Sem.rawNearSemiring n)
  module RSMv = RawRightSemimodule (V.rawRightSemimodule Sem.rawNearSemiring n)

  module +G   = Group Ri.+-group
  module VGrp = RawGroup (V.rawGroup +G.rawGroup n)

  open RingProperties CR.ring n public

  +ᴹ-*-isCommutativeRing :
    IsCommutativeRing RSv._≈_ RSv._+_ RSv._*_ VGrp._⁻¹ RSv.0# RSv.1#
  +ᴹ-*-isCommutativeRing = record
    { isRing = +ᴹ-*-isRing
    ; *-comm = λ xs ys i → CR.*-comm (xs i) (ys i)
    }

  isModule :
    IsModule cRing RNSv._≈_ RNSv._+_ RNSv.0# VGrp._⁻¹ LSMv._*ₗ_ RSMv._*ᵣ_
  isModule = record
    { isBimodule         = isBimodule
    ; *ₗ-*ᵣ-coincident   = λ r xs i → CR.*-comm r (xs i)
    }

  ⟨module⟩ : Module _ _ _
  ⟨module⟩ = record { isModule = isModule }
