------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of polymorphic versions of standard definitions in
-- Relation.Unary
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Unary.Polymorphic.Properties where

open import Level using (Level)
open import Relation.Binary.Definitions hiding (Decidable; Universal)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Unary hiding (∅; U)
open import Relation.Unary.Polymorphic
open import Data.Unit.Polymorphic.Base using (tt)

private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A : Set a

----------------------------------------------------------------------
-- The empty set

∅? : Decidable {A = A} {ℓ} ∅
∅? _ = no λ()

∅-Empty : Empty {A = A} {ℓ} ∅
∅-Empty _ ()

∁∅-Universal : Universal {A = A} {ℓ} (∁ ∅)
∁∅-Universal _ ()

----------------------------------------------------------------------
-- The universe

U? : Decidable {A = A} {ℓ} U
U? _ = yes tt

U-Universal : Universal {A = A} {ℓ} U
U-Universal _ = _

∁U-Empty : Empty {A = A} {ℓ} (∁ U)
∁U-Empty _ x∈∁U = x∈∁U _

----------------------------------------------------------------------
-- Subset properties

∅-⊆ : (P : Pred A ℓ₁) → ∅ {ℓ = ℓ₂} ⊆ P
∅-⊆ _ ()

⊆-U : (P : Pred A ℓ₁) → P ⊆ U {ℓ = ℓ₂}
⊆-U _ _ = _

⊆-min : Min {A = Pred A ℓ₁} {B = Pred A ℓ₂} _⊆_ ∅
⊆-min = ∅-⊆

⊆-max : Max {A = Pred A ℓ₁} {B = Pred A ℓ₂} _⊆_ U
⊆-max = ⊆-U

∅-⊆′ : (P : Pred A ℓ₁) → ∅ {ℓ = ℓ₂} ⊆′ P
∅-⊆′ _ _ = λ ()

⊆′-U : (P : Pred A ℓ₁) → P ⊆′ U {ℓ = ℓ₂}
⊆′-U _ _ _ = _

⊆′-min : Min {A = Pred A ℓ₁} {B = Pred A ℓ₂} _⊆′_ ∅
⊆′-min = ∅-⊆′

⊆′-max : Max {A = Pred A ℓ₁} {B = Pred A ℓ₂} _⊆′_ U
⊆′-max = ⊆′-U
