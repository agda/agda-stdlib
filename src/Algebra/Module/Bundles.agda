------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of algebraic structures defined over some other
-- structure, like modules and vector spaces
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Module.Bundles where

open import Algebra.Bundles
open import Algebra.Module.Structures
open import Algebra.FunctionProperties.Core
import Algebra.FunctionProperties.LeftAction as LFP
import Algebra.FunctionProperties.RightAction as RFP
open import Function.Base
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
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    isLeftSemimodule : IsLeftSemimodule _≈ᴹ_ semiring _+ᴹ_ _*ₗ_ 0ᴹ

  open IsLeftSemimodule isLeftSemimodule public

  +ᴹ-commutativeMonoid : CommutativeMonoid m ℓm
  +ᴹ-commutativeMonoid = record
    { isCommutativeMonoid = +ᴹ-isCommutativeMonoid
    }

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
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    -ᴹ_ : Op₁ Carrierᴹ
    isLeftModule : IsLeftModule _≈ᴹ_ ring _+ᴹ_ _*ₗ_ 0ᴹ -ᴹ_

  open IsLeftModule isLeftModule public

  leftSemimodule : LeftSemimodule semiring m ℓm
  leftSemimodule = record { isLeftSemimodule = isLeftSemimodule }

  open LeftSemimodule leftSemimodule public
    using ( +ᴹ-commutativeMonoid; +ᴹ-monoid; +ᴹ-semigroup; +ᴹ-magma
          ; +ᴹ-rawMagma; +ᴹ-rawMonoid)

  +ᴹ-abelianGroup : AbelianGroup m ℓm
  +ᴹ-abelianGroup = record { isAbelianGroup = +ᴹ-isAbelianGroup }

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
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ᵣ_ : Opᵣ Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    isRightSemimodule : IsRightSemimodule _≈ᴹ_ semiring _+ᴹ_ _*ᵣ_ 0ᴹ

  open IsRightSemimodule isRightSemimodule public

  +ᴹ-commutativeMonoid : CommutativeMonoid m ℓm
  +ᴹ-commutativeMonoid = record
    { isCommutativeMonoid = +ᴹ-isCommutativeMonoid
    }

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
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ᵣ_ : Opᵣ Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    -ᴹ_ : Op₁ Carrierᴹ
    isRightModule : IsRightModule _≈ᴹ_ ring _+ᴹ_ _*ᵣ_ 0ᴹ -ᴹ_

  open IsRightModule isRightModule public

  rightSemimodule : RightSemimodule semiring m ℓm
  rightSemimodule = record { isRightSemimodule = isRightSemimodule }

  open RightSemimodule rightSemimodule public
    using ( +ᴹ-commutativeMonoid; +ᴹ-monoid; +ᴹ-semigroup; +ᴹ-magma
          ; +ᴹ-rawMagma; +ᴹ-rawMonoid)

  +ᴹ-abelianGroup : AbelianGroup m ℓm
  +ᴹ-abelianGroup = record { isAbelianGroup = +ᴹ-isAbelianGroup }

  open AbelianGroup +ᴹ-abelianGroup public
    using ()
    renaming (group to +ᴹ-group)

------------------------------------------------------------------------
-- Bimodules
------------------------------------------------------------------------

record Bisemimodule {r s ℓr ℓs} (R-semiring : Semiring r ℓr)
                                (S-semiring : Semiring s ℓs) m ℓm
                    : Set (r ⊔ s ⊔ ℓr ⊔ ℓs ⊔ suc (m ⊔ ℓm)) where
  private
    module R = Semiring R-semiring
    module S = Semiring S-semiring

  infixr 7 _*ₗ_
  infixl 6 _+ᴹ_
  infix 4 _≈ᴹ_

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ R.Carrier Carrierᴹ
    _*ᵣ_ : Opᵣ S.Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    isBisemimodule : IsBisemimodule _≈ᴹ_ R-semiring S-semiring _+ᴹ_ _*ₗ_ _*ᵣ_ 0ᴹ

  open IsBisemimodule isBisemimodule public

  leftSemimodule : LeftSemimodule R-semiring m ℓm
  leftSemimodule = record { isLeftSemimodule = isLeftSemimodule }

  rightSemimodule : RightSemimodule S-semiring m ℓm
  rightSemimodule = record { isRightSemimodule = isRightSemimodule }

  open LeftSemimodule leftSemimodule public
    using ( +ᴹ-commutativeMonoid; +ᴹ-monoid; +ᴹ-semigroup; +ᴹ-magma; +ᴹ-rawMagma
          ; +ᴹ-rawMonoid)

record Bimodule {r s ℓr ℓs} (R-ring : Ring r ℓr) (S-ring : Ring s ℓs) m ℓm
                : Set (r ⊔ s ⊔ ℓr ⊔ ℓs ⊔ suc (m ⊔ ℓm)) where
  private
    module R = Ring R-ring
    module S = Ring S-ring

  infixr 7 _*ₗ_
  infixl 6 _+ᴹ_
  infix 4 _≈ᴹ_

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ R.Carrier Carrierᴹ
    _*ᵣ_ : Opᵣ S.Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    -ᴹ_ : Op₁ Carrierᴹ
    isBimodule : IsBimodule _≈ᴹ_ R-ring S-ring _+ᴹ_ _*ₗ_ _*ᵣ_ 0ᴹ -ᴹ_

  open IsBimodule isBimodule public

  leftModule : LeftModule R-ring m ℓm
  leftModule = record { isLeftModule = isLeftModule }

  rightModule : RightModule S-ring m ℓm
  rightModule = record { isRightModule = isRightModule }

  open LeftModule leftModule public
    using ( +ᴹ-abelianGroup; +ᴹ-commutativeMonoid; +ᴹ-group; +ᴹ-monoid
          ; +ᴹ-semigroup; +ᴹ-magma; +ᴹ-rawMagma; +ᴹ-rawMonoid)

  bisemimodule : Bisemimodule R.semiring S.semiring m ℓm
  bisemimodule = record { isBisemimodule = isBisemimodule }

  open Bisemimodule bisemimodule public
    using (leftSemimodule; rightSemimodule)

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
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ Carrier Carrierᴹ
    _*ᵣ_ : Opᵣ Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    isSemimodule : IsSemimodule _≈ᴹ_ commutativeSemiring _+ᴹ_ _*ₗ_ _*ᵣ_ 0ᴹ

  open IsSemimodule isSemimodule public

  private
    module L = LFP Carrier _≈ᴹ_
    module R = RFP Carrier _≈ᴹ_

  bisemimodule : Bisemimodule semiring semiring m ℓm
  bisemimodule = record { isBisemimodule = isBisemimodule }

  open Bisemimodule bisemimodule public
    using ( leftSemimodule; rightSemimodule
          ; +ᴹ-commutativeMonoid; +ᴹ-monoid; +ᴹ-semigroup; +ᴹ-magma; +ᴹ-rawMagma
          ; +ᴹ-rawMonoid)

  *ₗ-comm : L.Commutative _*ₗ_
  *ₗ-comm x y m =
    M-trans (M-sym (*ₗ-assoc x y m))
            (M-trans (*ₗ-cong (*-comm _ _) M-refl)
                     (*ₗ-assoc y x m))

  *ᵣ-comm : R.Commutative _*ᵣ_
  *ᵣ-comm m x y =
    M-trans (*ᵣ-assoc m x y)
            (M-trans (*ᵣ-cong M-refl (*-comm _ _))
                     (M-sym (*ᵣ-assoc m y x)))

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
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ Carrier Carrierᴹ
    _*ᵣ_ : Opᵣ Carrier Carrierᴹ
    0ᴹ : Carrierᴹ
    -ᴹ_ : Op₁ Carrierᴹ
    isModule : IsModule _≈ᴹ_ commutativeRing _+ᴹ_ _*ₗ_ _*ᵣ_ 0ᴹ -ᴹ_

  open IsModule isModule public

  bimodule : Bimodule ring ring m ℓm
  bimodule = record { isBimodule = isBimodule }

  open Bimodule bimodule public
    using ( leftModule; rightModule; leftSemimodule; rightSemimodule
          ; +ᴹ-abelianGroup; +ᴹ-group; +ᴹ-commutativeMonoid; +ᴹ-monoid
          ; +ᴹ-semigroup; +ᴹ-magma ; +ᴹ-rawMonoid; +ᴹ-rawMagma)

  semimodule : Semimodule commutativeSemiring m ℓm
  semimodule = record { isSemimodule = isSemimodule }

  open Semimodule semimodule public using (*ₗ-comm; *ᵣ-comm)
