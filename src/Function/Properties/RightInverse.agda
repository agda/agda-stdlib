------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversions for right inverses
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Properties.RightInverse where

open import Function.Base
open import Function.Bundles
open import Level using (Level)
open import Data.Product
open import Relation.Binary using (Setoid; IsEquivalence)

private
  variable
    ℓ₁ ℓ₂ a b : Level

module _ (A : Setoid a ℓ₁) (B : Setoid b ℓ₂) where

  RightInverse⇒Surjection : RightInverse A B → Surjection B A
  RightInverse⇒Surjection I = record
    { f = g
    ; cong = cong₂
    ; surjective = λ a → f a , inverseʳ a }
    where open RightInverse I

------------------------------------------------------------------------
-- Conversion functions

module _ {A : Set a} {B : Set b} where

  ↪⇒↠ : B ↪ A → A ↠ B
  ↪⇒↠ = RightInverse⇒Surjection _ _
