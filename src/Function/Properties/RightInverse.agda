------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of right inverses
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Properties.RightInverse where

open import Function.Base
open import Function.Definitions
open import Function.Bundles
open import Function.Consequences using (inverseˡ⇒surjective)
open import Level using (Level)
open import Data.Product.Base using (_,_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

private
  variable
    ℓ₁ ℓ₂ a b : Level
    A B : Set a
    S T : Setoid a ℓ₁

------------------------------------------------------------------------
-- Constructors

mkRightInverse : (e : Equivalence S T) (open Equivalence e) →
                 Inverseʳ Eq₁._≈_ Eq₂._≈_ to from →
                 RightInverse S T
mkRightInverse eq invʳ = record
  { Equivalence eq
  ; inverseʳ = invʳ
  }

------------------------------------------------------------------------
-- Conversion

RightInverse⇒LeftInverse : RightInverse S T → LeftInverse T S
RightInverse⇒LeftInverse I = record
  { to         = from
  ; from       = to
  ; to-cong    = from-cong
  ; from-cong  = to-cong
  ; inverseˡ   = inverseʳ
  } where open RightInverse I

LeftInverse⇒RightInverse : LeftInverse S T → RightInverse T S
LeftInverse⇒RightInverse I = record
  { to         = from
  ; from       = to
  ; to-cong    = from-cong
  ; from-cong  = to-cong
  ; inverseʳ    = inverseˡ
  } where open LeftInverse I

RightInverse⇒Surjection : RightInverse S T → Surjection T S
RightInverse⇒Surjection I = record
  { to         = from
  ; cong       = from-cong
  ; surjective = inverseˡ⇒surjective Eq₁._≈_ inverseʳ
  } where open RightInverse I

↪⇒↠ : B ↪ A → A ↠ B
↪⇒↠ = RightInverse⇒Surjection

↪⇒↩ : B ↪ A → A ↩ B
↪⇒↩ = RightInverse⇒LeftInverse

↩⇒↪ : B ↩ A → A ↪ B
↩⇒↪ = LeftInverse⇒RightInverse

------------------------------------------------------------------------
-- Other

module _ (R : RightInverse S T) where
  open RightInverse R

  to-from : ∀ {x y} → to x Eq₂.≈ y → from y Eq₁.≈ x
  to-from eq = Eq₁.trans (from-cong (Eq₂.sym eq)) (strictlyInverseʳ _)
