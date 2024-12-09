------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing vectors
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Show where

import Data.List.Show as List
open import Data.String.Base using (String)
open import Data.Vec.Base using (Vec; toList)
open import Function.Base using (_∘_)

show : ∀ {a} {A : Set a} {n} → (A → String) → (Vec A n → String)
show s = List.show s ∘ toList
