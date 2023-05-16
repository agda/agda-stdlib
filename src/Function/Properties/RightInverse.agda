------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversions for right inverses
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Properties.RightInverse where

open import Function.Base
open import Function.Bundles
open import Function.Consequences using (inverseʳ⇒surjective)
open import Level using (Level)
open import Data.Product
open import Relation.Binary using (Setoid; IsEquivalence)

private
  variable
    ℓ₁ ℓ₂ a b : Level
    A : Set a
    B : Set b
    S : Setoid a ℓ₁
    T : Setoid b ℓ₂

RightInverse⇒Surjection : RightInverse S T → Surjection T S
RightInverse⇒Surjection I = record
  { to         = from
  ; cong       = from-cong
  ; surjective = λ a → to a , inverseʳ a
  } where open RightInverse I

↪⇒↠ : B ↪ A → A ↠ B
↪⇒↠ = RightInverse⇒Surjection
