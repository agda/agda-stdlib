------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversions for surjections
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Properties.Surjection where

open import Function.Base
open import Function.Bundles
open import Level using (Level)
open import Data.Product

private
  variable
    a b : Level
    A B : Set a

------------------------------------------------------------------------
-- Conversion functions

↠⇒↪ : A ↠ B → B ↪ A
↠⇒↪ s = mk↪ {to = proj₁ ∘ surjective} {from = to} (proj₂ ∘ surjective)
  where open Surjection s

↠⇒⇔ : A ↠ B → A ⇔ B
↠⇒⇔ s = mk⇔ to (proj₁ ∘ surjective)
  where open Surjection s
