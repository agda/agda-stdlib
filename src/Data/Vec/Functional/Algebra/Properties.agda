------------------------------------------------------------------------
-- The Agda standard library
--
-- Some Vector-related module properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Functional.Algebra.Properties where

open import Level using (Level)
open import Function using (_$_; flip)
open import Data.Product hiding (map)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec.Functional
open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Module
open import Relation.Binary
import Algebra.Definitions as ADefinitions
open import Algebra.Structures
open import Data.Vec.Functional.Algebra.Base
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as Pointwise

private variable
  a ℓ : Level
  A : Set ℓ
  n : ℕ

------------------------------------------------------------------------
-- Algebraic properties of _+ᴹ_ -ᴹ_ _*ₗ_

module RawMagmaProperties (rawMagma : RawMagma a ℓ) where
  open VecMagma rawMagma
  open IsEquivalence
  private
    module ≈ = ADefinitions _≈_
    module ≈ᴹ {n} = ADefinitions (_≈ᴹ_ {n = n})

  ≈ᴹ-isEquivalence : IsEquivalence _≈_ → IsEquivalence (_≈ᴹ_ {n = n})
  ≈ᴹ-isEquivalence = flip Pointwise.isEquivalence _

  ∙ᴹ-cong : ≈.Congruent₂ _∙_ → ≈ᴹ.Congruent₂ (_∙ᴹ_ {n = n})
  ∙ᴹ-cong ∙-cong x≈y u≈v i = ∙-cong (x≈y i) (u≈v i)

  ∙ᴹ-assoc : ≈.Associative _∙_ → ≈ᴹ.Associative (_∙ᴹ_ {n})
  ∙ᴹ-assoc ∙-assoc xs ys zs i = ∙-assoc (xs i) (ys i) (zs i)

  ∙ᴹ-comm : ≈.Commutative _∙_ → ≈ᴹ.Commutative (_∙ᴹ_ {n})
  ∙ᴹ-comm ∙-comm xs ys i = ∙-comm (xs i) (ys i)


  -- isMagma : IsMagma _≈_ _∙_ → IsMagma _≈ᴹ_ (_∙ᴹ_ {n})
  -- isMagma isMagma = record
  --   { isEquivalence = ≈ᴹ-isEquivalence isEquivalence
  --   ; ∙-cong = ∙ᴹ-cong ∙-cong
  --   } where open IsMagma isMagma

  -- isCommutativeMagma : IsCommutativeMagma _≈_ _∙_ → IsCommutativeMagma _≈ᴹ_ (_∙ᴹ_ {n})
  -- isCommutativeMagma isCMagma = record
  --   { isMagma = isMagma CM.isMagma
  --   ; comm = ∙ᴹ-comm CM.comm
  --   } where module CM = IsCommutativeMagma isCMagma

  -- isSemigroup : IsSemigroup _≈_ _∙_ → IsSemigroup _≈ᴹ_ (_∙ᴹ_ {n})
  -- isSemigroup isSemigroup = record
  --   { isMagma = isMagma SG.isMagma
  --   ; assoc = ∙ᴹ-assoc SG.assoc
  --   } where module SG = IsSemigroup isSemigroup

  -- isCommutativeSemigroup : IsCommutativeSemigroup _≈_ _∙_ → IsCommutativeSemigroup _≈ᴹ_ (_∙ᴹ_ {n})
  -- isCommutativeSemigroup isCommutativeSemigroup = record
  --   { isSemigroup = isSemigroup SG.isSemigroup
  --   ; comm = ∙ᴹ-comm SG.comm
  --   } where module SG = IsCommutativeSemigroup isCommutativeSemigroup

module RawMonoidProperties (rawMonoid : RawMonoid a ℓ) where
  open VecMonoid rawMonoid
  open RawMagmaProperties rawMagma public
  private
    module ≈ = ADefinitions _≈_
    module ≈ᴹ {n} = ADefinitions (_≈ᴹ_ {n = n})

  ∙ᴹ-identityˡ : ≈.LeftIdentity ε _∙_ → ≈ᴹ.LeftIdentity (εᴹ {n}) _∙ᴹ_
  ∙ᴹ-identityˡ ∙-identityˡ xs i = ∙-identityˡ (xs i)

  ∙ᴹ-identityʳ : ≈.RightIdentity ε _∙_ → ≈ᴹ.RightIdentity (εᴹ {n}) _∙ᴹ_
  ∙ᴹ-identityʳ ∙-identityʳ xs is = ∙-identityʳ (xs is)

  ∙ᴹ-identity : ≈.Identity ε _∙_ → ≈ᴹ.Identity (εᴹ {n}) _∙ᴹ_
  ∙ᴹ-identity (∙-identityˡ , ∙-identityʳ) = ∙ᴹ-identityˡ ∙-identityˡ , ∙ᴹ-identityʳ ∙-identityʳ


  -- isMonoid : IsMonoid _≈_ _∙_ ε → IsMonoid _≈ᴹ_ (_∙ᴹ_ {n}) εᴹ
  -- isMonoid isMonoid = record
  --   { isSemigroup = isSemigroup M.isSemigroup
  --   ; identity = ∙ᴹ-identity M.identity
  --   } where module M = IsMonoid isMonoid

  -- isCommutativeMonoid : IsCommutativeMonoid _≈_ _∙_ ε → IsCommutativeMonoid _≈ᴹ_ (_∙ᴹ_ {n}) εᴹ
  -- isCommutativeMonoid isCommutativeMonoid = record
  --   { isMonoid = isMonoid CM.isMonoid
  --   ; comm = ∙ᴹ-comm CM.comm
  --   } where module CM = IsCommutativeMonoid isCommutativeMonoid


module RawGroupProperties (rawGroup : RawGroup a ℓ) where
  open VecGroup rawGroup renaming (_⁻¹ to -_)
  open RawMonoidProperties rawMonoid public
  private
    module ≈ = ADefinitions _≈_
    module ≈ᴹ {n} = ADefinitions (_≈ᴹ_ {n = n})

  -ᴹ‿inverseˡ : ≈.LeftInverse ε -_ _∙_ → ≈ᴹ.LeftInverse (εᴹ {n}) -ᴹ_ _∙ᴹ_
  -ᴹ‿inverseˡ -‿inverseˡ xs i = -‿inverseˡ (xs i)

  -ᴹ‿inverseʳ : ≈.RightInverse ε -_ _∙_ → ≈ᴹ.RightInverse (εᴹ {n}) -ᴹ_ _∙ᴹ_
  -ᴹ‿inverseʳ -‿inverseʳ xs i = -‿inverseʳ (xs i)

  -ᴹ‿inverse : ≈.Inverse ε -_ _∙_ → ≈ᴹ.Inverse (εᴹ {n}) -ᴹ_ _∙ᴹ_
  -ᴹ‿inverse (-‿inverseˡ , -‿inverseʳ) = -ᴹ‿inverseˡ -‿inverseˡ , -ᴹ‿inverseʳ -‿inverseʳ

  -ᴹ‿cong : ≈.Congruent₁ -_ → ≈ᴹ.Congruent₁ (-ᴹ_ {n})
  -ᴹ‿cong -‿cong xs i = -‿cong (xs i)


--   isGroup : IsGroup _≈_ _∙_ ε -_ → IsGroup _≈ᴹ_ (_∙ᴹ_ {n}) εᴹ -ᴹ_
--   isGroup isGroup = record
--     { isMonoid = isMonoid G.isMonoid
--     ; inverse = -ᴹ‿inverse G.inverse
--     ; ⁻¹-cong = -ᴹ‿cong G.⁻¹-cong
--     } where module G = IsGroup isGroup

--   isAbelianGroup : IsAbelianGroup _≈_ _∙_ ε -_ → IsAbelianGroup _≈ᴹ_ (_∙ᴹ_ {n}) εᴹ -ᴹ_
--   isAbelianGroup isAbelianGroup = record
--     { isGroup = isGroup AG.isGroup
--     ; comm = ∙ᴹ-comm AG.comm
--     } where module AG = IsAbelianGroup isAbelianGroup

module VecNearSemiringProperties (rawNearSemiring : RawNearSemiring a ℓ) where
  open VecNearSemiring rawNearSemiring
  open RawMagmaProperties *-rawMagma public using () renaming
    ( ∙ᴹ-comm to *ᴹ-comm
    ; ∙ᴹ-assoc to *ᴹ-assoc
    ; ∙ᴹ-cong to *ᴹ-cong
    )
  open RawMonoidProperties +-rawMonoid public renaming
    ( ∙ᴹ-comm to +ᴹ-comm
    ; ∙ᴹ-identity to +ᴹ-identity
    )
  private
    module LD≈ = LeftDefs Carrier _≈_
    module RD≈ = RightDefs Carrier _≈_
    module BD≈ = BiDefs Carrier Carrier _≈_
    module LD {n} = LeftDefs Carrier (_≈ᴹ_ {n = n})
    module RD {n} = RightDefs Carrier (_≈ᴹ_ {n = n})
    module BD {n} = BiDefs Carrier Carrier (_≈ᴹ_ {n = n})
    module ≈ = ADefinitions _≈_
    module ≈ᴹ {n} = ADefinitions (_≈ᴹ_ {n = n})

  *ₗ-cong : ≈.Congruent₂ _*_ → LD.Congruent _≈_ (_*ₗ_ {n})
  *ₗ-cong *-cong x≈y u≈v i = *-cong x≈y (u≈v i)

  *ₗ-zeroˡ : ≈.LeftZero 0# _*_ → LD.LeftZero 0# 0ᴹ (_*ₗ_ {n})
  *ₗ-zeroˡ zeroˡ xs i = zeroˡ (xs i)

  *ₗ-distribʳ : _*_ ≈.DistributesOverʳ _+_ → _*ₗ_ LD.DistributesOverʳ _+_ ⟶ _+ᴹ_ {n}
  *ₗ-distribʳ distribʳ xs m n i = distribʳ (xs i) m n

  *ₗ-assoc : ≈.Associative _*_ → LD.Associative _*_ (_*ₗ_ {n})
  *ₗ-assoc *-assoc m n xs i = *-assoc m n (xs i)

  *ₗ-zeroʳ : ≈.RightZero 0# _*_ → LD.RightZero (0ᴹ {n}) _*ₗ_
  *ₗ-zeroʳ zeroʳ m _ = zeroʳ m

  *ₗ-distribˡ : _*_ ≈.DistributesOverˡ _+_ → _*ₗ_ LD.DistributesOverˡ (_+ᴹ_ {n})
  *ₗ-distribˡ distribˡ m xs ys i = distribˡ m (xs i) (ys i)

  *ᵣ-cong : RD≈.Congruent _≈_ _*_ → RD.Congruent _≈_ (_*ᵣ_ {n})
  *ᵣ-cong *-cong x≈y u≈v i = *-cong (x≈y i) u≈v

  *ᵣ-distribˡ : _*_ RD≈.DistributesOverˡ _+_ ⟶ _+_ → _*ᵣ_ RD.DistributesOverˡ _+_ ⟶ (_+ᴹ_ {n})
  *ᵣ-distribˡ distribˡ xs m n i = distribˡ (xs i) m n

  *ᵣ-zeroˡ : RD≈.LeftZero 0# _*_ → RD.LeftZero (0ᴹ {n}) _*ᵣ_
  *ᵣ-zeroˡ zeroˡ xs i = zeroˡ xs

  *ᵣ-assoc : RD≈.Associative _*_ _*_ → RD.Associative _*_ (_*ᵣ_ {n})
  *ᵣ-assoc *-assoc xs m n i = *-assoc (xs i) m n

  *ᵣ-zeroʳ : RD≈.RightZero 0# 0# _*_ → RD.RightZero 0# (0ᴹ {n}) _*ᵣ_
  *ᵣ-zeroʳ zeroʳ xs i = zeroʳ (xs i)

  *ᵣ-distribʳ : _*_ RD≈.DistributesOverʳ _+_ → _*ᵣ_ RD.DistributesOverʳ (_+ᴹ_ {n})
  *ᵣ-distribʳ distribʳ xs m n i = distribʳ xs (m i) (n i)

  *ₗ-*ᵣ-assoc : BD≈.Associative _*_ _*_ → BD.Associative (_*ₗ_ {n}) _*ᵣ_
  *ₗ-*ᵣ-assoc *-assoc m xs n i = *-assoc m (xs i) n

  *ᴹ-zeroˡ : ≈.LeftZero 0# _*_ → ≈ᴹ.LeftZero (0ᴹ {n}) _*ᴹ_
  *ᴹ-zeroˡ zeroˡ xs i = zeroˡ (xs i)

  *ᴹ-zeroʳ : ≈.RightZero 0# _*_ → ≈ᴹ.RightZero (0ᴹ {n}) _*ᴹ_
  *ᴹ-zeroʳ zeroʳ xs i = zeroʳ (xs i)

  *ᴹ-zero : ≈.Zero 0# _*_ → ≈ᴹ.Zero (0ᴹ {n}) _*ᴹ_
  *ᴹ-zero (*-zeroˡ , *-zeroʳ) = *ᴹ-zeroˡ *-zeroˡ , *ᴹ-zeroʳ *-zeroʳ

  *ᴹ-+ᴹ-distribˡ : _*_ ≈.DistributesOverˡ _+_ → (_*ᴹ_ {n}) ≈ᴹ.DistributesOverˡ _+ᴹ_
  *ᴹ-+ᴹ-distribˡ distribˡ xs ys zs i = distribˡ (xs i) (ys i) (zs i)

  *ᴹ-+ᴹ-distribʳ : _*_ ≈.DistributesOverʳ _+_ → (_*ᴹ_ {n}) ≈ᴹ.DistributesOverʳ _+ᴹ_
  *ᴹ-+ᴹ-distribʳ distribʳ xs ys zs i = distribʳ (xs i) (ys i) (zs i)

  *ᴹ-+ᴹ-distrib : _*_ ≈.DistributesOver _+_ → (_*ᴹ_ {n}) ≈ᴹ.DistributesOver _+ᴹ_
  *ᴹ-+ᴹ-distrib (*-+-distribˡ , *-+-distribʳ) = *ᴹ-+ᴹ-distribˡ *-+-distribˡ , *ᴹ-+ᴹ-distribʳ *-+-distribʳ


module VecSemiRingProperties (rawSemiring : RawSemiring a ℓ) where
  open VecSemiring rawSemiring
  open VecNearSemiringProperties rawNearSemiring public
  open RawMonoidProperties *-rawMonoid public using () renaming
    ( ∙ᴹ-identity to *ᴹ-identity
    )
  private
    module LD≈ = LeftDefs Carrier _≈_
    module RD≈ = RightDefs Carrier _≈_
    module BD≈ = BiDefs Carrier Carrier _≈_
    module LD {n} = LeftDefs Carrier (_≈ᴹ_ {n = n})
    module RD {n} = RightDefs Carrier (_≈ᴹ_ {n = n})
    module BD {n} = BiDefs Carrier Carrier (_≈ᴹ_ {n = n})
    module ≈ = ADefinitions _≈_
    module ≈ᴹ {n} = ADefinitions (_≈ᴹ_ {n = n})

  *ₗ-identityˡ : ≈.LeftIdentity 1# _*_ → LD.LeftIdentity 1# (_*ₗ_ {n})
  *ₗ-identityˡ *-identityˡ xs i = *-identityˡ (xs i)

  *ᵣ-identityʳ : RD≈.RightIdentity 1# _*_ → RD.RightIdentity 1# (_*ᵣ_ {n})
  *ᵣ-identityʳ *-identityʳ xs i = *-identityʳ (xs i)

module MagmaProperties (magma : Magma a ℓ) where
  open Magma magma
  open VecMagma rawMagma
  open RawMagmaProperties rawMagma public

  ∙ᴹ-isMagma : IsMagma _≈ᴹ_ (_∙ᴹ_ {n})
  ∙ᴹ-isMagma = record
    { isEquivalence = ≈ᴹ-isEquivalence isEquivalence
    ; ∙-cong = ∙ᴹ-cong ∙-cong
    }

module CommutativeMagmaProperties (commutativeMagma : CommutativeMagma a ℓ) where
  open CommutativeMagma commutativeMagma
  open VecMagma rawMagma
  open MagmaProperties magma public

  ∙ᴹ-isCommutativeMagma : IsCommutativeMagma _≈ᴹ_ (_∙ᴹ_ {n})
  ∙ᴹ-isCommutativeMagma = record
    { isMagma = ∙ᴹ-isMagma
    ; comm = ∙ᴹ-comm comm
    }

module SemiRawGroupProperties (semigroup : Semigroup a ℓ) where
  open Semigroup semigroup
  open VecMagma rawMagma
  open MagmaProperties magma public

  ∙ᴹ-isSemigroup : IsSemigroup _≈ᴹ_ (_∙ᴹ_ {n})
  ∙ᴹ-isSemigroup = record
    { isMagma = ∙ᴹ-isMagma
    ; assoc = ∙ᴹ-assoc assoc
    }

module CommutativeSemigroupProperties (commutativeSemigroup : CommutativeSemigroup a ℓ) where
  open CommutativeSemigroup commutativeSemigroup
  open VecMagma rawMagma
  open SemiRawGroupProperties semigroup public

  ∙ᴹ-isCommutativeSemigroup : IsCommutativeSemigroup _≈ᴹ_ (_∙ᴹ_ {n})
  ∙ᴹ-isCommutativeSemigroup = record
    { isSemigroup = ∙ᴹ-isSemigroup
    ; comm = ∙ᴹ-comm comm
    }

module MonoidProperties (monoid : Monoid a ℓ) where
  open Monoid monoid
  open VecMonoid rawMonoid
  open RawMonoidProperties rawMonoid public using (∙ᴹ-identity)
  open SemiRawGroupProperties semigroup public

  ∙ᴹ-isMonoid : IsMonoid _≈ᴹ_ (_∙ᴹ_ {n}) εᴹ
  ∙ᴹ-isMonoid = record
    { isSemigroup = ∙ᴹ-isSemigroup
    ; identity = ∙ᴹ-identity identity
    }

module CommutativeMonoidProperties (commutativeMonoid : CommutativeMonoid a ℓ) where
  open CommutativeMonoid commutativeMonoid
  open VecMonoid rawMonoid
  open MonoidProperties monoid public

  ∙ᴹ-isCommutativeMonoid : IsCommutativeMonoid _≈ᴹ_ (_∙ᴹ_ {n}) εᴹ
  ∙ᴹ-isCommutativeMonoid = record
    { isMonoid = ∙ᴹ-isMonoid
    ; comm = ∙ᴹ-comm comm
    }

module GroupProperties (group : Group a ℓ) where
  open Group group
  open VecGroup rawGroup
  open RawGroupProperties rawGroup public using (-ᴹ‿inverse; -ᴹ‿cong)
  open MonoidProperties monoid public

  ∙ᴹ-isGroup : IsGroup _≈ᴹ_ (_∙ᴹ_ {n}) εᴹ -ᴹ_
  ∙ᴹ-isGroup = record
    { isMonoid = ∙ᴹ-isMonoid
    ; inverse = -ᴹ‿inverse inverse
    ; ⁻¹-cong = -ᴹ‿cong ⁻¹-cong
    }

module AbelianGroupProperties (abelianGroup : AbelianGroup a ℓ) where
  open AbelianGroup abelianGroup
  open VecGroup rawGroup
  open GroupProperties group public

  ∙ᴹ-isAbelianGroup : IsAbelianGroup _≈ᴹ_ (_∙ᴹ_ {n}) εᴹ -ᴹ_
  ∙ᴹ-isAbelianGroup = record
    { isGroup = ∙ᴹ-isGroup
    ; comm = ∙ᴹ-comm comm
    }

module NearSemiringProperties (nearSemiring : NearSemiring a ℓ) where
  open NearSemiring nearSemiring
  open VecNearSemiring rawNearSemiring
  open VecNearSemiringProperties rawNearSemiring public
  open MonoidProperties +-monoid public using (∙ᴹ-isMonoid)

  +ᴹ-*-isNearSemiring : IsNearSemiring _≈ᴹ_ (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ
  +ᴹ-*-isNearSemiring = record
    { +-isMonoid = ∙ᴹ-isMonoid
    ; *-cong = *ᴹ-cong *-cong
    ; *-assoc = *ᴹ-assoc *-assoc
    ; distribʳ = *ᴹ-+ᴹ-distribʳ distribʳ
    ; zeroˡ = *ᴹ-zeroˡ zeroˡ
    }

module SemiringWithoutOneProperties (semiringWithoutOne : SemiringWithoutOne a ℓ) where
  open SemiringWithoutOne semiringWithoutOne
  open VecNearSemiring rawNearSemiring
  open NearSemiringProperties nearSemiring public
  open CommutativeMonoidProperties +-commutativeMonoid public using (∙ᴹ-isCommutativeMonoid)

  +ᴹ-*-isSemiringWithoutOne : IsSemiringWithoutOne _≈ᴹ_ (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ
  +ᴹ-*-isSemiringWithoutOne = record
    { +-isCommutativeMonoid = ∙ᴹ-isCommutativeMonoid
    ; *-cong = *ᴹ-cong *-cong
    ; *-assoc = *ᴹ-assoc *-assoc
    ; distrib = *ᴹ-+ᴹ-distrib distrib
    ; zero = *ᴹ-zero (SemiringWithoutOne.zero semiringWithoutOne)
    }


module CommutativeSemiringWithoutOneProperties
  (commutativeSemiringWithoutOne : CommutativeSemiringWithoutOne a ℓ) where

  open CommutativeSemiringWithoutOne commutativeSemiringWithoutOne
  open VecNearSemiring rawNearSemiring
  open SemiringWithoutOneProperties semiringWithoutOne public

  +ᴹ-*-isCommutativeSemiringWithoutOne : IsCommutativeSemiringWithoutOne _≈ᴹ_ (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ
  +ᴹ-*-isCommutativeSemiringWithoutOne = record
    {isSemiringWithoutOne = +ᴹ-*-isSemiringWithoutOne
    ; *-comm = *ᴹ-comm *-comm
    }

module SemiringWithoutAnnihilatingZeroProperties
  (semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero a ℓ) where

  open SemiringWithoutAnnihilatingZero semiringWithoutAnnihilatingZero
  open VecSemiring rawSemiring
  open VecSemiRingProperties rawSemiring public
  open CommutativeMonoidProperties +-commutativeMonoid public using (∙ᴹ-isCommutativeMonoid)

  +ᴹ-*-isSemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero _≈ᴹ_ (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ 1ᴹ
  +ᴹ-*-isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = ∙ᴹ-isCommutativeMonoid
    ; *-cong = *ᴹ-cong *-cong
    ; *-assoc = *ᴹ-assoc *-assoc
    ; *-identity = *ᴹ-identity *-identity
    ; distrib = *ᴹ-+ᴹ-distrib distrib
    }

module SemiringProperties (semiring : Semiring a ℓ) where
  open Semiring semiring
  open VecSemiring rawSemiring
  open SemiringWithoutAnnihilatingZeroProperties semiringWithoutAnnihilatingZero public

  isPreleftSemimodule : IsPreleftSemimodule semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ₗ_
  isPreleftSemimodule = record
    { *ₗ-cong = *ₗ-cong *-cong
    ; *ₗ-zeroˡ = *ₗ-zeroˡ zeroˡ
    ; *ₗ-distribʳ = *ₗ-distribʳ distribʳ
    ; *ₗ-identityˡ = *ₗ-identityˡ *-identityˡ
    ; *ₗ-assoc = *ₗ-assoc *-assoc
    ; *ₗ-zeroʳ = *ₗ-zeroʳ zeroʳ
    ; *ₗ-distribˡ = *ₗ-distribˡ distribˡ
    }

  isPrerightSemimodule : IsPrerightSemimodule semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ᵣ_
  isPrerightSemimodule = record
    { *ᵣ-cong = *ᵣ-cong *-cong
    ; *ᵣ-zeroʳ = *ᵣ-zeroʳ zeroʳ
    ; *ᵣ-distribˡ = *ᵣ-distribˡ distribˡ
    ; *ᵣ-identityʳ = *ᵣ-identityʳ *-identityʳ
    ; *ᵣ-assoc = *ᵣ-assoc *-assoc
    ; *ᵣ-zeroˡ = *ᵣ-zeroˡ zeroˡ
    ; *ᵣ-distribʳ = *ᵣ-distribʳ distribʳ
    }

  isRightSemimodule : IsRightSemimodule semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ᵣ_
  isRightSemimodule = record
    { +ᴹ-isCommutativeMonoid = ∙ᴹ-isCommutativeMonoid
    ; isPrerightSemimodule = isPrerightSemimodule
    }

  isBisemimodule : IsBisemimodule semiring semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ₗ_ _*ᵣ_
  isBisemimodule = record
    { +ᴹ-isCommutativeMonoid = ∙ᴹ-isCommutativeMonoid
    ; isPreleftSemimodule = isPreleftSemimodule
    ; isPrerightSemimodule = isPrerightSemimodule
    ; *ₗ-*ᵣ-assoc = *ₗ-*ᵣ-assoc *-assoc
    }

  isLeftSemimodule : IsLeftSemimodule semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ₗ_
  isLeftSemimodule = record
    { +ᴹ-isCommutativeMonoid = ∙ᴹ-isCommutativeMonoid
    ; isPreleftSemimodule = isPreleftSemimodule
    }

  +ᴹ-*-isSemiring : IsSemiring _≈ᴹ_ (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ 1ᴹ
  +ᴹ-*-isSemiring = record
    { isSemiringWithoutAnnihilatingZero = +ᴹ-*-isSemiringWithoutAnnihilatingZero
    ; zero = *ᴹ-zero (Semiring.zero semiring)
    }

module CommutativeSemiringProperties (commutativeSemiring : CommutativeSemiring a ℓ) where
  open CommutativeSemiring commutativeSemiring
  open VecSemiring rawSemiring
  open SemiringProperties semiring

  +ᴹ-*-isCommutativeSemiring : IsCommutativeSemiring _≈ᴹ_ (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ 1ᴹ
  +ᴹ-*-isCommutativeSemiring = record
    { isSemiring = +ᴹ-*-isSemiring
    ; *-comm = *ᴹ-comm *-comm
    }

module RingWithoutOneProperties (ringWithoutOne : RingWithoutOne a ℓ) where
  open RingWithoutOne ringWithoutOne

  rawNearSemiring : RawNearSemiring a ℓ
  rawNearSemiring = record
    { Carrier = Carrier
    ; _≈_ = _≈_
    ; _+_ = _+_
    ; _*_ = _*_
    ; 0# = 0#
    }

  open Group +-group renaming (rawGroup to +-rawGroup) using ()
  open VecGroup +-rawGroup using (-ᴹ_)
  open AbelianGroupProperties +-abelianGroup using (∙ᴹ-isAbelianGroup) public
  open VecNearSemiring rawNearSemiring
  open VecNearSemiringProperties rawNearSemiring public

  +ᴹ-*-isRingWithoutOne : IsRingWithoutOne _≈ᴹ_ (_+ᴹ_ {n}) _*ᴹ_ -ᴹ_ 0ᴹ
  +ᴹ-*-isRingWithoutOne = record
    { +-isAbelianGroup = ∙ᴹ-isAbelianGroup
    ; *-cong = *ᴹ-cong *-cong
    ; *-assoc = *ᴹ-assoc *-assoc
    ; distrib = *ᴹ-+ᴹ-distrib distrib
    ; zero = *ᴹ-zero (RingWithoutOne.zero ringWithoutOne)
    }

module RingProperties (ring : Ring a ℓ) where
  open Ring ring
  open VecRing rawRing
  open Group +-group using (rawGroup)
  open AbelianGroupProperties +-abelianGroup public
    using (∙ᴹ-isAbelianGroup; -ᴹ‿cong; -ᴹ‿inverse)
  open SemiringProperties semiring public

  isRightModule : IsRightModule ring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ -ᴹ_ _*ᵣ_
  isRightModule = record
    { isRightSemimodule = isRightSemimodule
    ; -ᴹ‿cong = -ᴹ‿cong -‿cong
    ; -ᴹ‿inverse = -ᴹ‿inverse -‿inverse
    }

  isBimodule : IsBimodule ring ring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_ _*ᵣ_
  isBimodule = record
    { isBisemimodule = isBisemimodule
    ; -ᴹ‿cong = -ᴹ‿cong -‿cong
    ; -ᴹ‿inverse = -ᴹ‿inverse -‿inverse
    }

  isLeftModule : IsLeftModule ring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_
  isLeftModule = record
    { isLeftSemimodule = isLeftSemimodule
    ; -ᴹ‿cong = -ᴹ‿cong -‿cong
    ; -ᴹ‿inverse = -ᴹ‿inverse -‿inverse
    }

  +ᴹ-*-isRing : IsRing _≈ᴹ_ (_+ᴹ_ {n}) _*ᴹ_ -ᴹ_ 0ᴹ 1ᴹ
  +ᴹ-*-isRing = record
    { +-isAbelianGroup = ∙ᴹ-isAbelianGroup
    ; *-cong = *ᴹ-cong *-cong
    ; *-assoc = *ᴹ-assoc *-assoc
    ; *-identity = *ᴹ-identity *-identity
    ; distrib = *ᴹ-+ᴹ-distrib distrib
    ; zero = *ᴹ-zero (Ring.zero ring)
    }

module CommutativeRingProperties (commutativeRing : CommutativeRing a ℓ) where
  open CommutativeRing commutativeRing
  open VecRing rawRing
  open RingProperties ring public

  +ᴹ-*-isCommutativeRing : IsCommutativeRing _≈ᴹ_ (_+ᴹ_ {n}) _*ᴹ_ -ᴹ_ 0ᴹ 1ᴹ
  +ᴹ-*-isCommutativeRing = record
    { isRing = +ᴹ-*-isRing
    ; *-comm = *ᴹ-comm *-comm
    }

  isModule : IsModule commutativeRing (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_ _*ᵣ_
  isModule = record
    { isBimodule = isBimodule
    }


-- ------------------------------------------------------------------------
-- -- Structures

-- *ᴹ-isSemigroup : IsSemigroup (_*ᴹ_ {n})
-- *ᴹ-isSemigroup = record
--   { isMagma = *ᴹ-isMagma
--   ; assoc = *ᴹ-assoc
--   }

-- *ᴹ-isMonoid : IsMonoid (_*ᴹ_ {n}) 1ᴹ
-- *ᴹ-isMonoid = record
--   { isSemigroup = *ᴹ-isSemigroup
--   ; identity = *ᴹ-identity
--   }



-- ------------------------------------------------------------------------
-- -- Bundles

-- magma : ℕ → Magma _ _
-- magma n = record
--   { isMagma = isMagma {n}
--   }

-- *ᴹ-magma : ℕ → Magma _ _
-- *ᴹ-magma n = record
--   { isMagma = *ᴹ-isMagma {n}
--   }

-- commutativeMagma : ℕ → CommutativeMagma _ _
-- commutativeMagma n = record {
--   isCommutativeMagma = isCommutativeMagma {n}
--   }

-- semigroup : ℕ → Semigroup _ _
-- semigroup n = record
--   { isSemigroup = isSemigroup {n}
--   }

-- *ᴹ-semigroup : ℕ → Semigroup _ _
-- *ᴹ-semigroup n = record
--   { isSemigroup = *ᴹ-isSemigroup {n}
--   }

-- commutativeSemigroup : ℕ → CommutativeSemigroup _ _
-- commutativeSemigroup n = record
--   { isCommutativeSemigroup = isCommutativeSemigroup {n}
--   }

-- monoid : ℕ → Monoid _ _
-- monoid n = record
--   { isMonoid = isMonoid {n}
--   }

-- *ᴹ-monoid : ℕ → Monoid _ _
-- *ᴹ-monoid n = record
--   { isMonoid = *ᴹ-isMonoid {n}
--   }

-- commutativeMonoid : ℕ → CommutativeMonoid _ _
-- commutativeMonoid n = record
--   { isCommutativeMonoid = isCommutativeMonoid {n}
--   }

-- group : ℕ → Group _ _
-- group n = record
--   { isGroup = isGroup {n}
--   }

-- leftSemimodule : ℕ → LeftSemimodule _ _ _
-- leftSemimodule n = record
--   { isLeftSemimodule = isLeftSemimodule {n}
--   }

-- leftModule : ℕ → LeftModule _ _ _
-- leftModule n = record
--   { isLeftModule = isLeftModule {n}
--   }

-- bisemimodule : ℕ → Bisemimodule _ _ _ _
-- bisemimodule n = record
--   { isBisemimodule = isBisemimodule {n}
--   }

-- rightModule : ℕ → RightModule _ _ _
-- rightModule n = record
--   { isRightModule = isRightModule {n}
--   }

-- bimodule : ℕ → Bimodule _ _ _ _
-- bimodule n = record
--   { isBimodule = isBimodule {n}
--   }

-- module' : ℕ → Module _ _ _
-- module' n = record
--   { isModule = isModule {n}
--   }

-- +ᴹ-*-nearSemiring : ℕ → NearSemiring _ _
-- +ᴹ-*-nearSemiring n = record
--   { isNearSemiring = +ᴹ-*-isNearSemiring {n}
--   }

-- +ᴹ-*-semiringWithoutOne : ℕ → SemiringWithoutOne _ _
-- +ᴹ-*-semiringWithoutOne n = record
--   { isSemiringWithoutOne = +ᴹ-*-isSemiringWithoutOne {n}
--   }

-- +ᴹ-*-commutativeSemiringWithoutOne : ℕ → CommutativeSemiringWithoutOne _ _
-- +ᴹ-*-commutativeSemiringWithoutOne n = record
--   { isCommutativeSemiringWithoutOne = +ᴹ-*-isCommutativeSemiringWithoutOne {n}
--   }

-- +ᴹ-*-semiringWithoutAnnihilatingZero : ℕ → SemiringWithoutAnnihilatingZero _ _
-- +ᴹ-*-semiringWithoutAnnihilatingZero n = record
--   { isSemiringWithoutAnnihilatingZero = +ᴹ-*-isSemiringWithoutAnnihilatingZero {n}
--   }

-- +ᴹ-*-semiring : ℕ → Semiring _ _
-- +ᴹ-*-semiring n = record
--   { isSemiring = +ᴹ-*-isSemiring {n}
--   }

-- +ᴹ-*-commutativeSemiring : ℕ → CommutativeSemiring _ _
-- +ᴹ-*-commutativeSemiring n = record
--   { isCommutativeSemiring = +ᴹ-*-isCommutativeSemiring {n}
--   }

-- +ᴹ-*-ringWithoutOne : ℕ → RingWithoutOne _ _
-- +ᴹ-*-ringWithoutOne n = record
--   { isRingWithoutOne = +ᴹ-*-isRingWithoutOne {n}
--   }
