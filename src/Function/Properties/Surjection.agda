------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversions for surjections
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
↠⇒↪ s = mk↪ {f = proj₁ ∘ surjective} {g = f} (proj₂ ∘ surjective)
  where open Surjection s

↠⇒⇔ : A ↠ B → A ⇔ B
↠⇒⇔ s = mk⇔ f (proj₁ ∘ surjective)
  where open Surjection s
