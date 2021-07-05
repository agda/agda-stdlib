------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversions for surjections
--   This file is meant to be imported qualified.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Properties.Surjection where

open import Function.Base
open import Function.Bundles
open import Level using (Level)
open import Data.Product

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Conversion functions

↠⇒↪ : A ↠ B → B ↪ A
↠⇒↪ record { f = f ; cong = cong ; surjective = surjective } =
  mk↪ {f = proj₁ ∘ surjective} {g = f} (proj₂ ∘ surjective)

↠⇒⇔ : A ↠ B → A ⇔ B
↠⇒⇔ record { f = f ; cong = cong ; surjective = surjective } =
  mk⇔ f (proj₁ ∘ surjective)
