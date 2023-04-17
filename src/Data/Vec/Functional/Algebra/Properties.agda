------------------------------------------------------------------------
-- The Agda standard library
--
-- Some Vector-related module properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Function using (_$_)
open import Data.Product hiding (map)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec.Functional
open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Module
open import Relation.Binary
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as VecSetoid
import Algebra.Definitions as AD
import Algebra.Structures as AS
import Data.Vec.Functional.Algebra.Base as VFA

module Data.Vec.Functional.Algebra.Properties
  {c ℓ} (ring : Ring c ℓ) where

private variable
  n : ℕ

open Ring ring
open VecSetoid setoid
open VFA ring
module SR = Semiring semiring
open module AD' {n} = AD (_≈ᴹ_ {n})
open module AS' {n} = AS (_≈ᴹ_ {n})
module LD {n} = LeftDefs Carrier (_≈ᴹ_ {n})
module RD {n} = RightDefs Carrier (_≈ᴹ_ {n})
module BD {n} = BiDefs Carrier Carrier (_≈ᴹ_ {n})

------------------------------------------------------------------------
-- Algebraic properties of _+ᴹ_ -ᴹ_ _*ₗ_

+ᴹ-cong : Congruent₂ (_+ᴹ_ {n})
+ᴹ-cong x≈y u≈v i = +-cong (x≈y i) (u≈v i)

+ᴹ-assoc : Associative (_+ᴹ_ {n})
+ᴹ-assoc xs ys zs i = +-assoc (xs i) (ys i) (zs i)

+ᴹ-comm : Commutative (_+ᴹ_ {n})
+ᴹ-comm xs ys i = +-comm (xs i) (ys i)

+ᴹ-identityˡ : LeftIdentity (0ᴹ {n}) _+ᴹ_
+ᴹ-identityˡ xs i = +-identityˡ (xs i)

+ᴹ-identityʳ : RightIdentity (0ᴹ {n}) _+ᴹ_
+ᴹ-identityʳ xs is = +-identityʳ (xs is)

+ᴹ-identity : Identity (0ᴹ {n}) _+ᴹ_
+ᴹ-identity = +ᴹ-identityˡ , +ᴹ-identityʳ

-ᴹ‿cong : Congruent₁ (-ᴹ_ {n})
-ᴹ‿cong xs i = -‿cong (xs i)

-ᴹ‿inverseˡ : AD'.LeftInverse (0ᴹ {n}) -ᴹ_ _+ᴹ_
-ᴹ‿inverseˡ xs i = -‿inverseˡ (xs i)

-ᴹ‿inverseʳ : AD'.RightInverse (0ᴹ {n}) -ᴹ_ _+ᴹ_
-ᴹ‿inverseʳ xs i = -‿inverseʳ (xs i)

-ᴹ‿inverse : AD'.Inverse (0ᴹ {n}) -ᴹ_ _+ᴹ_
-ᴹ‿inverse = -ᴹ‿inverseˡ , -ᴹ‿inverseʳ

*ₗ-cong : LD.Congruent SR._≈_ (_*ₗ_ {n})
*ₗ-cong x≈y u≈v i = *-cong x≈y (u≈v i)

*ₗ-zeroˡ : LD.LeftZero SR.0# (0ᴹ {n}) _*ₗ_
*ₗ-zeroˡ xs i = zeroˡ (xs i)

*ₗ-distribʳ : _*ₗ_ LD.DistributesOverʳ SR._+_ ⟶ (_+ᴹ_ {n})
*ₗ-distribʳ xs m n i = distribʳ (xs i) m n

*ₗ-identityˡ : LD.LeftIdentity SR.1# (_*ₗ_ {n})
*ₗ-identityˡ xs i = *-identityˡ (xs i)

*ₗ-assoc : LD.Associative SR._*_ (_*ₗ_ {n})
*ₗ-assoc m n xs i = *-assoc m n (xs i)

*ₗ-zeroʳ : LD.RightZero (0ᴹ {n}) _*ₗ_
*ₗ-zeroʳ m _ = zeroʳ m

*ₗ-distribˡ : _*ₗ_ LD.DistributesOverˡ (_+ᴹ_ {n})
*ₗ-distribˡ m xs ys i = distribˡ m (xs i) (ys i)

*ᵣ-cong : RD.Congruent SR._≈_ (_*ᵣ_ {n})
*ᵣ-cong x≈y u≈v i = *-cong (x≈y i) u≈v

*ᵣ-distribˡ : _*ᵣ_ RD.DistributesOverˡ SR._+_ ⟶ (_+ᴹ_ {n})
*ᵣ-distribˡ xs m n i = distribˡ (xs i) m n

*ᵣ-zeroˡ : RD.LeftZero (0ᴹ {n}) _*ᵣ_
*ᵣ-zeroˡ xs i = zeroˡ xs

*ᵣ-identityʳ : RD.RightIdentity SR.1# (_*ᵣ_ {n})
*ᵣ-identityʳ xs i = *-identityʳ (xs i)

*ᵣ-assoc : RD.Associative SR._*_ (_*ᵣ_ {n})
*ᵣ-assoc xs m n i = *-assoc (xs i) m n

*ᵣ-zeroʳ : RD.RightZero SR.0# (0ᴹ {n}) _*ᵣ_
*ᵣ-zeroʳ xs i = zeroʳ (xs i)

*ᵣ-distribʳ : _*ᵣ_ RD.DistributesOverʳ (_+ᴹ_ {n})
*ᵣ-distribʳ xs m n i = distribʳ xs (m i) (n i)

*ₗ-*ᵣ-assoc : BD.Associative (_*ₗ_ {n}) _*ᵣ_
*ₗ-*ᵣ-assoc m xs n i = *-assoc m (xs i) n

------------------------------------------------------------------------
-- Structures

isMagma : IsMagma (_+ᴹ_ {n})
isMagma = record
  { isEquivalence = ≋-isEquivalence _
  ; ∙-cong = +ᴹ-cong
  }

isCommutativeMagma : IsCommutativeMagma (_+ᴹ_ {n})
isCommutativeMagma = record
  { isMagma = isMagma
  ; comm = +ᴹ-comm
  }

isSemigroup : IsSemigroup (_+ᴹ_ {n})
isSemigroup = record
  { isMagma = isMagma
  ; assoc = +ᴹ-assoc
  }

isCommutativeSemigroup : IsCommutativeSemigroup (_+ᴹ_ {n})
isCommutativeSemigroup = record
  { isSemigroup = isSemigroup
  ; comm = +ᴹ-comm
  }

isMonoid : IsMonoid (_+ᴹ_ {n}) 0ᴹ
isMonoid = record
  { isSemigroup = isSemigroup
  ; identity = +ᴹ-identity
  }

isCommutativeMonoid : IsCommutativeMonoid (_+ᴹ_ {n}) 0ᴹ
isCommutativeMonoid = record
  { isMonoid = isMonoid
  ; comm = +ᴹ-comm
  }

isGroup : IsGroup (_+ᴹ_ {n}) 0ᴹ -ᴹ_
isGroup = record
  { isMonoid = isMonoid
  ; inverse = -ᴹ‿inverse
  ; ⁻¹-cong = -ᴹ‿cong
  }

isAbelianGroup : IsAbelianGroup (_+ᴹ_ {n}) 0ᴹ -ᴹ_
isAbelianGroup = record
  { isGroup = isGroup
  ; comm = +ᴹ-comm
  }

isPreleftSemimodule : IsPreleftSemimodule semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ₗ_
isPreleftSemimodule = record
  { *ₗ-cong = *ₗ-cong
  ; *ₗ-zeroˡ = *ₗ-zeroˡ
  ; *ₗ-distribʳ = *ₗ-distribʳ
  ; *ₗ-identityˡ = *ₗ-identityˡ
  ; *ₗ-assoc = *ₗ-assoc
  ; *ₗ-zeroʳ = *ₗ-zeroʳ
  ; *ₗ-distribˡ = *ₗ-distribˡ
  }

isPrerightSemimodule : IsPrerightSemimodule semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ᵣ_
isPrerightSemimodule = record
  { *ᵣ-cong = *ᵣ-cong
  ; *ᵣ-zeroʳ = *ᵣ-zeroʳ
  ; *ᵣ-distribˡ = *ᵣ-distribˡ
  ; *ᵣ-identityʳ = *ᵣ-identityʳ
  ; *ᵣ-assoc = *ᵣ-assoc
  ; *ᵣ-zeroˡ = *ᵣ-zeroˡ
  ; *ᵣ-distribʳ = *ᵣ-distribʳ
  }

isRightSemimodule : IsRightSemimodule semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ᵣ_
isRightSemimodule = record
  { +ᴹ-isCommutativeMonoid = isCommutativeMonoid
  ; isPrerightSemimodule = isPrerightSemimodule
  }

isBisemimodule : IsBisemimodule semiring semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ₗ_ _*ᵣ_
isBisemimodule = record
  { +ᴹ-isCommutativeMonoid = isCommutativeMonoid
  ; isPreleftSemimodule = isPreleftSemimodule
  ; isPrerightSemimodule = isPrerightSemimodule
  ; *ₗ-*ᵣ-assoc = *ₗ-*ᵣ-assoc
  }

isRightModule : IsRightModule ring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ -ᴹ_ _*ᵣ_
isRightModule = record
  { isRightSemimodule = isRightSemimodule
  ; -ᴹ‿cong = -ᴹ‿cong
  ; -ᴹ‿inverse = -ᴹ‿inverse
  }

isBimodule : IsBimodule ring ring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_ _*ᵣ_
isBimodule = record
  { isBisemimodule = isBisemimodule
  ; -ᴹ‿cong = -ᴹ‿cong
  ; -ᴹ‿inverse = -ᴹ‿inverse
  }

isLeftSemimodule : IsLeftSemimodule semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ₗ_
isLeftSemimodule = record
  { +ᴹ-isCommutativeMonoid = isCommutativeMonoid
  ; isPreleftSemimodule = isPreleftSemimodule
  }

isLeftModule : IsLeftModule ring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_
isLeftModule = record
  { isLeftSemimodule = isLeftSemimodule
  ; -ᴹ‿cong = -ᴹ‿cong
  ; -ᴹ‿inverse = -ᴹ‿inverse
  }

------------------------------------------------------------------------
-- Bundles

magma : ℕ → Magma _ _
magma n = record
  { isMagma = isMagma {n}
  }

commutativeMagma : ℕ → CommutativeMagma _ _
commutativeMagma n = record {
  isCommutativeMagma = isCommutativeMagma {n}
  }

semigroup : ℕ → Semigroup _ _
semigroup n = record
  { isSemigroup = isSemigroup {n}
  }

commutativeSemigroup : ℕ → CommutativeSemigroup _ _
commutativeSemigroup n = record
  { isCommutativeSemigroup = isCommutativeSemigroup {n}
  }

monoid : ℕ → Monoid _ _
monoid n = record
  { isMonoid = isMonoid {n}
  }

commutativeMonoid : ℕ → CommutativeMonoid _ _
commutativeMonoid n = record
  { isCommutativeMonoid = isCommutativeMonoid {n}
  }

group : ℕ → Group _ _
group n = record
  { isGroup = isGroup {n}
  }

leftSemimodule : ℕ → LeftSemimodule _ _ _
leftSemimodule n = record
  { isLeftSemimodule = isLeftSemimodule {n}
  }

leftModule : ℕ → LeftModule _ _ _
leftModule n = record
  { isLeftModule = isLeftModule {n}
  }

bisemimodule : ℕ → Bisemimodule _ _ _ _
bisemimodule n = record
  { isBisemimodule = isBisemimodule {n}
  }

rightModule : ℕ → RightModule _ _ _
rightModule n = record
  { isRightModule = isRightModule {n}
  }

bimodule : ℕ → Bimodule _ _ _ _
bimodule n = record
  { isBimodule = isBimodule {n}
  }
