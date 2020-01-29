------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of algebraic structures defined over some other
-- structure, like modules and vector spaces
--
-- Terminology of bundles:
-- * There are both *semimodules* and *modules*.
--   - For M an R-semimodule, R is a semiring, and M forms a commutative
--     monoid.
--   - For M an R-module, R is a ring, and M forms an Abelian group.
-- * There are all four of *left modules*, *right modules*, *bimodules*,
--   and *modules*.
--   - Left modules have a left-scaling operation.
--   - Right modules have a right-scaling operation.
--   - Bimodules have two sorts of scalars. Left-scaling handles one and
--     right-scaling handles the other. Left-scaling and right-scaling
--     are furthermore compatible.
--   - Modules are bimodules with a single sort of scalars and scalar
--     multiplication must also be commutative. Left-scaling and
--     right-scaling coincide.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Module.Bundles where

open import Algebra.Bundles
open import Algebra.Core
open import Algebra.Module.Structures
open import Algebra.Module.Definitions
open import Function.Base
open import Level
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as SetR

private
  variable
    r ℓr s ℓs : Level

------------------------------------------------------------------------
-- Left modules
------------------------------------------------------------------------

record LeftSemimodule (semiring : Semiring r ℓr) m ℓm
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
    isLeftSemimodule : IsLeftSemimodule semiring _≈ᴹ_ _+ᴹ_ 0ᴹ _*ₗ_

  open IsLeftSemimodule isLeftSemimodule public

  +ᴹ-commutativeMonoid : CommutativeMonoid m ℓm
  +ᴹ-commutativeMonoid = record
    { isCommutativeMonoid = +ᴹ-isCommutativeMonoid
    }

  open CommutativeMonoid +ᴹ-commutativeMonoid public
    using () renaming
    ( monoid    to +ᴹ-monoid
    ; semigroup to +ᴹ-semigroup
    ; magma     to +ᴹ-magma
    ; rawMagma  to +ᴹ-rawMagma
    ; rawMonoid to +ᴹ-rawMonoid
    )

record LeftModule (ring : Ring r ℓr) m ℓm : Set (r ⊔ ℓr ⊔ suc (m ⊔ ℓm)) where
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
    isLeftModule : IsLeftModule ring _≈ᴹ_ _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_

  open IsLeftModule isLeftModule public

  leftSemimodule : LeftSemimodule semiring m ℓm
  leftSemimodule = record { isLeftSemimodule = isLeftSemimodule }

  open LeftSemimodule leftSemimodule public
    using ( +ᴹ-commutativeMonoid; +ᴹ-monoid; +ᴹ-semigroup; +ᴹ-magma
          ; +ᴹ-rawMagma; +ᴹ-rawMonoid)

  +ᴹ-abelianGroup : AbelianGroup m ℓm
  +ᴹ-abelianGroup = record { isAbelianGroup = +ᴹ-isAbelianGroup }

  open AbelianGroup +ᴹ-abelianGroup public
    using () renaming (group to +ᴹ-group)

------------------------------------------------------------------------
-- Right modules
------------------------------------------------------------------------

record RightSemimodule (semiring : Semiring r ℓr) m ℓm
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
    isRightSemimodule : IsRightSemimodule semiring _≈ᴹ_ _+ᴹ_ 0ᴹ _*ᵣ_

  open IsRightSemimodule isRightSemimodule public

  +ᴹ-commutativeMonoid : CommutativeMonoid m ℓm
  +ᴹ-commutativeMonoid = record
    { isCommutativeMonoid = +ᴹ-isCommutativeMonoid
    }

  open CommutativeMonoid +ᴹ-commutativeMonoid public
    using () renaming
    ( monoid    to +ᴹ-monoid
    ; semigroup to +ᴹ-semigroup
    ; magma     to +ᴹ-magma
    ; rawMagma  to +ᴹ-rawMagma
    ; rawMonoid to +ᴹ-rawMonoid
    )

record RightModule (ring : Ring r ℓr) m ℓm : Set (r ⊔ ℓr ⊔ suc (m ⊔ ℓm)) where
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
    isRightModule : IsRightModule ring _≈ᴹ_ _+ᴹ_ 0ᴹ -ᴹ_ _*ᵣ_

  open IsRightModule isRightModule public

  rightSemimodule : RightSemimodule semiring m ℓm
  rightSemimodule = record { isRightSemimodule = isRightSemimodule }

  open RightSemimodule rightSemimodule public
    using ( +ᴹ-commutativeMonoid; +ᴹ-monoid; +ᴹ-semigroup; +ᴹ-magma
          ; +ᴹ-rawMagma; +ᴹ-rawMonoid)

  +ᴹ-abelianGroup : AbelianGroup m ℓm
  +ᴹ-abelianGroup = record { isAbelianGroup = +ᴹ-isAbelianGroup }

  open AbelianGroup +ᴹ-abelianGroup public
    using () renaming (group to +ᴹ-group)

------------------------------------------------------------------------
-- Bimodules
------------------------------------------------------------------------

record Bisemimodule (R-semiring : Semiring r ℓr) (S-semiring : Semiring s ℓs)
                    m ℓm : Set (r ⊔ s ⊔ ℓr ⊔ ℓs ⊔ suc (m ⊔ ℓm)) where
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
    isBisemimodule : IsBisemimodule R-semiring S-semiring _≈ᴹ_ _+ᴹ_ 0ᴹ _*ₗ_ _*ᵣ_

  open IsBisemimodule isBisemimodule public

  leftSemimodule : LeftSemimodule R-semiring m ℓm
  leftSemimodule = record { isLeftSemimodule = isLeftSemimodule }

  rightSemimodule : RightSemimodule S-semiring m ℓm
  rightSemimodule = record { isRightSemimodule = isRightSemimodule }

  open LeftSemimodule leftSemimodule public
    using ( +ᴹ-commutativeMonoid; +ᴹ-monoid; +ᴹ-semigroup; +ᴹ-magma; +ᴹ-rawMagma
          ; +ᴹ-rawMonoid)

record Bimodule (R-ring : Ring r ℓr) (S-ring : Ring s ℓs) m ℓm
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
    isBimodule : IsBimodule R-ring S-ring _≈ᴹ_ _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_ _*ᵣ_

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

record Semimodule (commutativeSemiring : CommutativeSemiring r ℓr) m ℓm
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
    isSemimodule : IsSemimodule commutativeSemiring _≈ᴹ_ _+ᴹ_ 0ᴹ _*ₗ_ _*ᵣ_

  open IsSemimodule isSemimodule public

  private
    module L = LeftDefs Carrier _≈ᴹ_
    module R = RightDefs Carrier _≈ᴹ_

  bisemimodule : Bisemimodule semiring semiring m ℓm
  bisemimodule = record { isBisemimodule = isBisemimodule }

  open Bisemimodule bisemimodule public
    using ( leftSemimodule; rightSemimodule
          ; +ᴹ-commutativeMonoid; +ᴹ-monoid; +ᴹ-semigroup; +ᴹ-magma
          ; +ᴹ-rawMagma; +ᴹ-rawMonoid)

  open SetR ≈ᴹ-setoid

  *ₗ-comm : L.Commutative _*ₗ_
  *ₗ-comm x y m = begin
    x *ₗ y *ₗ m   ≈⟨ ≈ᴹ-sym (*ₗ-assoc x y m) ⟩
    (x * y) *ₗ m  ≈⟨ *ₗ-cong (*-comm _ _) ≈ᴹ-refl ⟩
    (y * x) *ₗ m  ≈⟨ *ₗ-assoc y x m ⟩
    y *ₗ x *ₗ m   ∎

  *ᵣ-comm : R.Commutative _*ᵣ_
  *ᵣ-comm m x y = begin
    m *ᵣ x *ᵣ y   ≈⟨ *ᵣ-assoc m x y ⟩
    m *ᵣ (x * y)  ≈⟨ *ᵣ-cong ≈ᴹ-refl (*-comm _ _) ⟩
    m *ᵣ (y * x)  ≈⟨ ≈ᴹ-sym (*ᵣ-assoc m y x) ⟩
    m *ᵣ y *ᵣ x   ∎

record Module (commutativeRing : CommutativeRing r ℓr) m ℓm
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
    isModule : IsModule commutativeRing _≈ᴹ_ _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_ _*ᵣ_

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
