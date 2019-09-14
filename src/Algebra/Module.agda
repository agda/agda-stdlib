------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of algebraic structures defined over some other
-- structure, like modules and vector spaces
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Module where

open import Algebra
import Algebra.Structures.Module as Str
open import Algebra.FunctionProperties.Core
open import Algebra.FunctionProperties.Module.Core
import Algebra.FunctionProperties.Module.Left as LFP
import Algebra.FunctionProperties.Module.Right as RFP
open import Function
open import Level
open import Relation.Binary

------------------------------------------------------------------------
-- Left modules
------------------------------------------------------------------------

record LeftSemimodule {r ℓr} (semiring : Semiring r ℓr) m ℓm
                      : Set (r ⊔ ℓr ⊔ suc (m ⊔ ℓm)) where
  open Semiring semiring

  infixr 7 _*ₗ_
  infixl 6 _+ᴹ_
  infix 4 _≈ᴹ_

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
  open Str _≈ᴹ_
  field
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    isLeftSemimodule : IsLeftSemimodule semiring _+ᴹ_ _*ₗ_ 0ᴹ

  open IsLeftSemimodule isLeftSemimodule public

  +ᴹ-commutativeMonoid : CommutativeMonoid m ℓm
  +ᴹ-commutativeMonoid =
    record { isCommutativeMonoid = +ᴹ-isCommutativeMonoid }

  open CommutativeMonoid +ᴹ-commutativeMonoid public
    using ()
    renaming ( monoid to +ᴹ-monoid; semigroup to +ᴹ-semigroup
             ; magma to +ᴹ-magma; rawMagma to +ᴹ-rawMagma
             ; rawMonoid to +ᴹ-rawMonoid)

record LeftModule {r ℓr} (ring : Ring r ℓr) m ℓm
                  : Set (r ⊔ ℓr ⊔ suc (m ⊔ ℓm)) where
  open Ring ring

  infixr 8 -ᴹ_
  infixr 7 _*ₗ_
  infixl 6 _+ᴹ_
  infix 4 _≈ᴹ_

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
  open Str _≈ᴹ_
  field
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    -ᴹ_ : Op₁ Carrierᴹ
    isLeftModule : IsLeftModule ring _+ᴹ_ _*ₗ_ 0ᴹ -ᴹ_

  open IsLeftModule isLeftModule public

  leftSemimodule : LeftSemimodule semiring m ℓm
  leftSemimodule = record { isLeftSemimodule = isLeftSemimodule }

  open LeftSemimodule leftSemimodule public
    using ( +ᴹ-commutativeMonoid; +ᴹ-monoid; +ᴹ-semigroup; +ᴹ-magma
          ; +ᴹ-rawMagma; +ᴹ-rawMonoid)

  +ᴹ-abelianGroup : AbelianGroup m ℓm
  +ᴹ-abelianGroup =
    record { isAbelianGroup = +ᴹ-isAbelianGroup }

  open AbelianGroup +ᴹ-abelianGroup public
    using ()
    renaming (group to +ᴹ-group)

------------------------------------------------------------------------
-- Right modules
------------------------------------------------------------------------

record RightSemimodule {r ℓr} (semiring : Semiring r ℓr) m ℓm
                       : Set (r ⊔ ℓr ⊔ suc (m ⊔ ℓm)) where
  open Semiring semiring

  infixl 7 _*ᵣ_
  infixl 6 _+ᴹ_
  infix 4 _≈ᴹ_

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
  open Str _≈ᴹ_
  field
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ᵣ_ : Opᵣ Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    isRightSemimodule : IsRightSemimodule semiring _+ᴹ_ _*ᵣ_ 0ᴹ

  open IsRightSemimodule isRightSemimodule public

  +ᴹ-commutativeMonoid : CommutativeMonoid m ℓm
  +ᴹ-commutativeMonoid =
    record { isCommutativeMonoid = +ᴹ-isCommutativeMonoid }

  open CommutativeMonoid +ᴹ-commutativeMonoid public
    using ()
    renaming ( monoid to +ᴹ-monoid; semigroup to +ᴹ-semigroup
             ; magma to +ᴹ-magma; rawMagma to +ᴹ-rawMagma
             ; rawMonoid to +ᴹ-rawMonoid)

record RightModule {r ℓr} (ring : Ring r ℓr) m ℓm
                   : Set (r ⊔ ℓr ⊔ suc (m ⊔ ℓm)) where
  open Ring ring

  infixr 8 -ᴹ_
  infixl 7 _*ᵣ_
  infixl 6 _+ᴹ_
  infix 4 _≈ᴹ_

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
  open Str _≈ᴹ_
  field
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ᵣ_ : Opᵣ Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    -ᴹ_ : Op₁ Carrierᴹ
    isRightModule : IsRightModule ring _+ᴹ_ _*ᵣ_ 0ᴹ -ᴹ_

  open IsRightModule isRightModule public

  rightSemimodule : RightSemimodule semiring m ℓm
  rightSemimodule = record { isRightSemimodule = isRightSemimodule }

  open RightSemimodule rightSemimodule public
    using ( +ᴹ-commutativeMonoid; +ᴹ-monoid; +ᴹ-semigroup; +ᴹ-magma
          ; +ᴹ-rawMagma; +ᴹ-rawMonoid)

  +ᴹ-abelianGroup : AbelianGroup m ℓm
  +ᴹ-abelianGroup =
    record { isAbelianGroup = +ᴹ-isAbelianGroup }

  open AbelianGroup +ᴹ-abelianGroup public
    using ()
    renaming (group to +ᴹ-group)

------------------------------------------------------------------------
-- Modules over commutative structures
------------------------------------------------------------------------

record Semimodule {r ℓr} (commutativeSemiring : CommutativeSemiring r ℓr) m ℓm
                  : Set (r ⊔ ℓr ⊔ suc (m ⊔ ℓm)) where
  open CommutativeSemiring commutativeSemiring

  infixr 7 _*ₗ_
  infixl 7 _*ᵣ_
  infixl 6 _+ᴹ_
  infix 4 _≈ᴹ_

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
  open Str _≈ᴹ_
  field
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    isSemimodule : IsSemimodule commutativeSemiring _+ᴹ_ _*ₗ_ 0ᴹ

  open IsSemimodule isSemimodule public

  private
    module L = LFP _≈_ _≈ᴹ_
    module R = RFP _≈_ _≈ᴹ_

  leftSemimodule : LeftSemimodule semiring m ℓm
  leftSemimodule = record { isLeftSemimodule = isLeftSemimodule }

  open LeftSemimodule leftSemimodule public
    using ( +ᴹ-commutativeMonoid; +ᴹ-monoid; +ᴹ-semigroup; +ᴹ-magma
          ; +ᴹ-rawMonoid; +ᴹ-rawMagma)

  _*ᵣ_ : Opᵣ Carrier Carrierᴹ
  _*ᵣ_ = flip _*ₗ_

  *ₗ-comm : L.Commutative _*ₗ_
  *ₗ-comm x y m =
    M-trans (M-sym (*ₗ-assoc x y m))
            (M-trans (*ₗ-cong (*-comm _ _) M-refl)
                     (*ₗ-assoc y x m))

  *ᵣ-comm : R.Commutative _*ᵣ_
  *ᵣ-comm m x y = *ₗ-comm y x m

  rightSemimodule : RightSemimodule semiring m ℓm
  rightSemimodule = record
    { Carrierᴹ = Carrierᴹ
    ; _≈ᴹ_ = _≈ᴹ_
    ; _+ᴹ_ = _+ᴹ_
    ; _*ᵣ_ = _*ᵣ_
    ; 0ᴹ = 0ᴹ
    ; isRightSemimodule = record
      { +ᴹ-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
      ; *ᵣ-cong = flip *ₗ-cong
      ; *ᵣ-zeroʳ = *ₗ-zeroˡ
      ; *ᵣ-distribˡ = λ m x y → *ₗ-distribʳ m x y
      ; *ᵣ-identityʳ = λ m → *ₗ-identityˡ m
      ; *ᵣ-assoc = λ m x y → M-trans (*ₗ-comm y x m) (M-sym (*ₗ-assoc x y m))
      ; *ᵣ-zeroˡ = *ₗ-zeroʳ
      ; *ᵣ-distribʳ = λ x m n → *ₗ-distribˡ x m n
      }
    }

  open RightSemimodule rightSemimodule public
    using ( *ᵣ-cong; *ᵣ-zeroʳ; *ᵣ-distribˡ; *ᵣ-identityʳ; *ᵣ-assoc; *ᵣ-zeroˡ
          ; *ᵣ-distribʳ; isRightSemimodule)

record Module {r ℓr} (commutativeRing : CommutativeRing r ℓr) m ℓm
              : Set (r ⊔ ℓr ⊔ suc (m ⊔ ℓm)) where
  open CommutativeRing commutativeRing

  infixr 8 -ᴹ_
  infixr 7 _*ₗ_
  infixl 6 _+ᴹ_
  infix 4 _≈ᴹ_

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
  open Str _≈ᴹ_
  field
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    -ᴹ_ : Op₁ Carrierᴹ
    isModule : IsModule commutativeRing _+ᴹ_ _*ₗ_ 0ᴹ -ᴹ_

  open IsModule isModule public

  semimodule : Semimodule commutativeSemiring m ℓm
  semimodule = record
    { _≈ᴹ_ = _≈ᴹ_
    ; _+ᴹ_ = _+ᴹ_
    ; _*ₗ_ = _*ₗ_
    ; 0ᴹ = 0ᴹ
    ; isSemimodule = isSemimodule
    }

  open Semimodule semimodule public
    using ( leftSemimodule; isLeftSemimodule; _*ᵣ_; *ₗ-comm; *ᵣ-comm
          ; rightSemimodule; isRightSemimodule; *ᵣ-cong; *ᵣ-zeroʳ; *ᵣ-distribˡ
          ; *ᵣ-identityʳ; *ᵣ-assoc; *ᵣ-zeroˡ; *ᵣ-distribʳ
          ; +ᴹ-commutativeMonoid; +ᴹ-monoid; +ᴹ-semigroup; +ᴹ-magma
          ; +ᴹ-rawMonoid; +ᴹ-rawMagma)

  leftModule : LeftModule ring m ℓm
  leftModule = record { isLeftModule = isLeftModule }

  open LeftModule leftModule public
    using (+ᴹ-abelianGroup; +ᴹ-group)

  isRightModule : IsRightModule ring _+ᴹ_ _*ᵣ_ 0ᴹ -ᴹ_
  isRightModule = record
    { isRightSemimodule = record
      { +ᴹ-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
      ; *ᵣ-cong = *ᵣ-cong
      ; *ᵣ-zeroʳ = *ᵣ-zeroʳ
      ; *ᵣ-distribˡ = *ᵣ-distribˡ
      ; *ᵣ-identityʳ = *ᵣ-identityʳ
      ; *ᵣ-assoc = *ᵣ-assoc
      ; *ᵣ-zeroˡ = *ᵣ-zeroˡ
      ; *ᵣ-distribʳ = *ᵣ-distribʳ
      }
    ; -ᴹ‿cong = -ᴹ‿cong
    ; -ᴹ‿inverse = -ᴹ‿inverse
    }

  rightModule : RightModule ring m ℓm
  rightModule = record { isRightModule = isRightModule }
