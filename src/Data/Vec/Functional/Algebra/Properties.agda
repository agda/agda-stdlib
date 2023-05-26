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

module MagmaProperties (rawMagma : RawMagma a ℓ) where
  open VecMagma rawMagma renaming (_∙_ to _+_)
  open IsEquivalence
  private
    module ≈ = ADefinitions _≈_
    module ≈ᴹ {n} = ADefinitions (_≈ᴹ_ {n = n})

  ≈ᴹ-isEquivalence : IsEquivalence _≈_ → IsEquivalence (_≈ᴹ_ {n = n})
  ≈ᴹ-isEquivalence = flip Pointwise.isEquivalence _

  +ᴹ-cong : ≈.Congruent₂ _+_ → ≈ᴹ.Congruent₂ (_+ᴹ_ {n = n})
  +ᴹ-cong +-cong x≈y u≈v i = +-cong (x≈y i) (u≈v i)

  +ᴹ-assoc : ≈.Associative _+_ → ≈ᴹ.Associative (_+ᴹ_ {n})
  +ᴹ-assoc +-assoc xs ys zs i = +-assoc (xs i) (ys i) (zs i)

  +ᴹ-comm : ≈.Commutative _+_ → ≈ᴹ.Commutative (_+ᴹ_ {n})
  +ᴹ-comm +-comm xs ys i = +-comm (xs i) (ys i)

  isMagma : IsMagma _≈_ _+_ → IsMagma _≈ᴹ_ (_+ᴹ_ {n})
  isMagma isMagma = record
    { isEquivalence = ≈ᴹ-isEquivalence isEquivalence
    ; ∙-cong = +ᴹ-cong ∙-cong
    } where open IsMagma isMagma


module MonoidProperties (rawMonoid : RawMonoid a ℓ) where
  open VecMonoid rawMonoid renaming (_∙_ to _+_; ε to 0#)
  open MagmaProperties rawMagma public
  private
    module ≈ = ADefinitions _≈_
    module ≈ᴹ {n} = ADefinitions (_≈ᴹ_ {n = n})

  +ᴹ-identityˡ : ≈.LeftIdentity 0# _+_ → ≈ᴹ.LeftIdentity (0ᴹ {n}) _+ᴹ_
  +ᴹ-identityˡ +-identityˡ xs i = +-identityˡ (xs i)

  +ᴹ-identityʳ : ≈.RightIdentity 0# _+_ → ≈ᴹ.RightIdentity (0ᴹ {n}) _+ᴹ_
  +ᴹ-identityʳ +-identityʳ xs is = +-identityʳ (xs is)

  +ᴹ-identity : ≈.Identity 0# _+_ → ≈ᴹ.Identity (0ᴹ {n}) _+ᴹ_
  +ᴹ-identity (+-identityˡ , +-identityʳ) = +ᴹ-identityˡ +-identityˡ , +ᴹ-identityʳ +-identityʳ


module GroupProperties (rawGroup : RawGroup a ℓ) where
  open VecGroup rawGroup renaming (_∙_ to _+_; ε to 0#; _⁻¹ to -_)
  open MonoidProperties rawMonoid public
  private
    module ≈ = ADefinitions _≈_
    module ≈ᴹ {n} = ADefinitions (_≈ᴹ_ {n = n})

  -ᴹ‿inverseˡ : ≈.LeftInverse 0# -_ _+_ → ≈ᴹ.LeftInverse (0ᴹ {n}) -ᴹ_ _+ᴹ_
  -ᴹ‿inverseˡ -‿inverseˡ xs i = -‿inverseˡ (xs i)

  -ᴹ‿inverseʳ : ≈.RightInverse 0# -_ _+_ → ≈ᴹ.RightInverse (0ᴹ {n}) -ᴹ_ _+ᴹ_
  -ᴹ‿inverseʳ -‿inverseʳ xs i = -‿inverseʳ (xs i)

  -ᴹ‿inverse : ≈.Inverse 0# -_ _+_ → ≈ᴹ.Inverse (0ᴹ {n}) -ᴹ_ _+ᴹ_
  -ᴹ‿inverse (-‿inverseˡ , -‿inverseʳ) = -ᴹ‿inverseˡ -‿inverseˡ , -ᴹ‿inverseʳ -‿inverseʳ

  -ᴹ‿cong : ≈.Congruent₁ -_ → ≈ᴹ.Congruent₁ (-ᴹ_ {n})
  -ᴹ‿cong -‿cong xs i = -‿cong (xs i)


module VecSemiRingProperties (rawSemiring : RawSemiring a ℓ) where
  open VecSemiring rawSemiring
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

  *ₗ-identityˡ : ≈.LeftIdentity 1# _*_ → LD.LeftIdentity 1# (_*ₗ_ {n})
  *ₗ-identityˡ *-identityˡ xs i = *-identityˡ (xs i)

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

  *ᵣ-identityʳ : RD≈.RightIdentity 1# _*_ → RD.RightIdentity 1# (_*ᵣ_ {n})
  *ᵣ-identityʳ *-identityʳ xs i = *-identityʳ (xs i)

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

-- module MultiplicationProperties (_*_ : Op₂ A) where
--   _*ᴹ_ : Op₂ $ Vector A n
--   _*ᴹ_ {n = n} = AB._*ᴹ_ {n = n} _*_

  -- *ᴹ-cong : Congruent₂ _≈_ _*_ → Congruent₂ _≈ᴹ_ (_*ᴹ_ {n = n})
  -- *ᴹ-cong *-cong x≈y u≈v i = *-cong (x≈y i) (u≈v i)

  -- *ᴹ-assoc : Associative (_*ᴹ_ {n})
  -- *ᴹ-assoc xs ys zs i = *-assoc (xs i) (ys i) (zs i)



-- ------------------------------------------------------------------------
-- -- Structures

-- *ᴹ-isMagma : IsMagma (_*ᴹ_ {n})
-- *ᴹ-isMagma = record
--   { isEquivalence = ≋-isEquivalence _
--   ; ∙-cong = *ᴹ-cong
--   }

-- isCommutativeMagma : IsCommutativeMagma (_+ᴹ_ {n})
-- isCommutativeMagma = record
--   { isMagma = isMagma
--   ; comm = +ᴹ-comm
--   }

-- isSemigroup : IsSemigroup (_+ᴹ_ {n})
-- isSemigroup = record
--   { isMagma = isMagma
--   ; assoc = +ᴹ-assoc
--   }

-- *ᴹ-isSemigroup : IsSemigroup (_*ᴹ_ {n})
-- *ᴹ-isSemigroup = record
--   { isMagma = *ᴹ-isMagma
--   ; assoc = *ᴹ-assoc
--   }

-- isCommutativeSemigroup : IsCommutativeSemigroup (_+ᴹ_ {n})
-- isCommutativeSemigroup = record
--   { isSemigroup = isSemigroup
--   ; comm = +ᴹ-comm
--   }

-- isMonoid : IsMonoid (_+ᴹ_ {n}) 0ᴹ
-- isMonoid = record
--   { isSemigroup = isSemigroup
--   ; identity = +ᴹ-identity
--   }

-- *ᴹ-isMonoid : IsMonoid (_*ᴹ_ {n}) 1ᴹ
-- *ᴹ-isMonoid = record
--   { isSemigroup = *ᴹ-isSemigroup
--   ; identity = *ᴹ-identity
--   }

-- isCommutativeMonoid : IsCommutativeMonoid (_+ᴹ_ {n}) 0ᴹ
-- isCommutativeMonoid = record
--   { isMonoid = isMonoid
--   ; comm = +ᴹ-comm
--   }

-- isGroup : IsGroup (_+ᴹ_ {n}) 0ᴹ -ᴹ_
-- isGroup = record
--   { isMonoid = isMonoid
--   ; inverse = -ᴹ‿inverse
--   ; ⁻¹-cong = -ᴹ‿cong
--   }

-- isAbelianGroup : IsAbelianGroup (_+ᴹ_ {n}) 0ᴹ -ᴹ_
-- isAbelianGroup = record
--   { isGroup = isGroup
--   ; comm = +ᴹ-comm
--   }

-- isPreleftSemimodule : IsPreleftSemimodule semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ₗ_
-- isPreleftSemimodule = record
--   { *ₗ-cong = *ₗ-cong
--   ; *ₗ-zeroˡ = *ₗ-zeroˡ
--   ; *ₗ-distribʳ = *ₗ-distribʳ
--   ; *ₗ-identityˡ = *ₗ-identityˡ
--   ; *ₗ-assoc = *ₗ-assoc
--   ; *ₗ-zeroʳ = *ₗ-zeroʳ
--   ; *ₗ-distribˡ = *ₗ-distribˡ
--   }

-- isPrerightSemimodule : IsPrerightSemimodule semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ᵣ_
-- isPrerightSemimodule = record
--   { *ᵣ-cong = *ᵣ-cong
--   ; *ᵣ-zeroʳ = *ᵣ-zeroʳ
--   ; *ᵣ-distribˡ = *ᵣ-distribˡ
--   ; *ᵣ-identityʳ = *ᵣ-identityʳ
--   ; *ᵣ-assoc = *ᵣ-assoc
--   ; *ᵣ-zeroˡ = *ᵣ-zeroˡ
--   ; *ᵣ-distribʳ = *ᵣ-distribʳ
--   }

-- isRightSemimodule : IsRightSemimodule semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ᵣ_
-- isRightSemimodule = record
--   { +ᴹ-isCommutativeMonoid = isCommutativeMonoid
--   ; isPrerightSemimodule = isPrerightSemimodule
--   }

-- isBisemimodule : IsBisemimodule semiring semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ₗ_ _*ᵣ_
-- isBisemimodule = record
--   { +ᴹ-isCommutativeMonoid = isCommutativeMonoid
--   ; isPreleftSemimodule = isPreleftSemimodule
--   ; isPrerightSemimodule = isPrerightSemimodule
--   ; *ₗ-*ᵣ-assoc = *ₗ-*ᵣ-assoc
--   }

-- isRightModule : IsRightModule ring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ -ᴹ_ _*ᵣ_
-- isRightModule = record
--   { isRightSemimodule = isRightSemimodule
--   ; -ᴹ‿cong = -ᴹ‿cong
--   ; -ᴹ‿inverse = -ᴹ‿inverse
--   }

-- isBimodule : IsBimodule ring ring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_ _*ᵣ_
-- isBimodule = record
--   { isBisemimodule = isBisemimodule
--   ; -ᴹ‿cong = -ᴹ‿cong
--   ; -ᴹ‿inverse = -ᴹ‿inverse
--   }

-- isLeftSemimodule : IsLeftSemimodule semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ₗ_
-- isLeftSemimodule = record
--   { +ᴹ-isCommutativeMonoid = isCommutativeMonoid
--   ; isPreleftSemimodule = isPreleftSemimodule
--   }

-- isLeftModule : IsLeftModule ring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_
-- isLeftModule = record
--   { isLeftSemimodule = isLeftSemimodule
--   ; -ᴹ‿cong = -ᴹ‿cong
--   ; -ᴹ‿inverse = -ᴹ‿inverse
--   }

-- isModule : IsModule cring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_ _*ᵣ_
-- isModule = record
--   { isBimodule = isBimodule
--   }

-- +ᴹ-*-isNearSemiring : IsNearSemiring (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ
-- +ᴹ-*-isNearSemiring = record
--   { +-isMonoid = isMonoid
--   ; *-cong = *ᴹ-cong
--   ; *-assoc = *ᴹ-assoc
--   ; distribʳ = *ᴹ-+ᴹ-distribʳ
--   ; zeroˡ = *ᴹ-zeroˡ
--   }

-- +ᴹ-*-isSemiringWithoutOne : IsSemiringWithoutOne (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ
-- +ᴹ-*-isSemiringWithoutOne = record
--   { +-isCommutativeMonoid = isCommutativeMonoid
--   ; *-cong = *ᴹ-cong
--   ; *-assoc = *ᴹ-assoc
--   ; distrib = *ᴹ-+ᴹ-distrib
--   ; zero = *ᴹ-zero
--   }

-- +ᴹ-*-isCommutativeSemiringWithoutOne : IsCommutativeSemiringWithoutOne (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ
-- +ᴹ-*-isCommutativeSemiringWithoutOne = record
--   {isSemiringWithoutOne = +ᴹ-*-isSemiringWithoutOne
--   ; *-comm = *ᴹ-comm
--   }

-- +ᴹ-*-isSemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ 1ᴹ
-- +ᴹ-*-isSemiringWithoutAnnihilatingZero = record
--   { +-isCommutativeMonoid = isCommutativeMonoid
--   ; *-cong = *ᴹ-cong
--   ; *-assoc = *ᴹ-assoc
--   ; *-identity = *ᴹ-identity
--   ; distrib = *ᴹ-+ᴹ-distrib
--   }

-- +ᴹ-*-isSemiring : IsSemiring (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ 1ᴹ
-- +ᴹ-*-isSemiring = record
--   { isSemiringWithoutAnnihilatingZero = +ᴹ-*-isSemiringWithoutAnnihilatingZero
--   ; zero = *ᴹ-zero
--   }

-- +ᴹ-*-isCommutativeSemiring : IsCommutativeSemiring (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ 1ᴹ
-- +ᴹ-*-isCommutativeSemiring = record
--   { isSemiring = +ᴹ-*-isSemiring
--   ; *-comm = *ᴹ-comm
--   }

-- +ᴹ-*-isRingWithoutOne : IsRingWithoutOne (_+ᴹ_ {n}) _*ᴹ_ -ᴹ_ 0ᴹ
-- +ᴹ-*-isRingWithoutOne = record
--   { +-isAbelianGroup = isAbelianGroup
--   ; *-cong = *ᴹ-cong
--   ; *-assoc = *ᴹ-assoc
--   ; distrib = *ᴹ-+ᴹ-distrib
--   ; zero = *ᴹ-zero
--   }

-- +ᴹ-*-isRing : IsRing (_+ᴹ_ {n}) _*ᴹ_ -ᴹ_ 0ᴹ 1ᴹ
-- +ᴹ-*-isRing = record
--   { +-isAbelianGroup = isAbelianGroup
--   ; *-cong = *ᴹ-cong
--   ; *-assoc = *ᴹ-assoc
--   ; *-identity = *ᴹ-identity
--   ; distrib = *ᴹ-+ᴹ-distrib
--   ; zero = *ᴹ-zero
--   }

-- +ᴹ-*-isCommutativeRing : IsCommutativeRing (_+ᴹ_ {n}) _*ᴹ_ -ᴹ_ 0ᴹ 1ᴹ
-- +ᴹ-*-isCommutativeRing = record
--   { isRing = +ᴹ-*-isRing
--   ; *-comm = *ᴹ-comm
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
