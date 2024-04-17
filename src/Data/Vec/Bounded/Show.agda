------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing bounded vectors
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Bounded.Show where

open import Data.String.Base using (String)
open import Data.Vec.Bounded.Base using (Vec≤)
import Data.Vec.Show as Vec
open import Function.Base using (_∘_)

show : ∀ {a} {A : Set a} {n} → (A → String) → (Vec≤ A n → String)
show s = Vec.show s ∘ Vec≤.vec
