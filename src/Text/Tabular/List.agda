------------------------------------------------------------------------
-- The Agda standard library
--
-- Fancy display functions for List-based tables
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Text.Tabular.List where

open import Data.String using (String)
open import Data.List.Base
import Data.Nat.Properties as ℕₚ
open import Data.Product using (-,_; proj₂)
open import Data.Vec.Base as Vec using (Vec)
open import Data.Vec.Bounded.Base as Vec≤ using (Vec≤)
open import Function.Base

open import Text.Tabular.Base
import Text.Tabular.Vec as Show

display : TabularConfig → List Alignment → List (List String) → List String
display c a rows = Show.display c alignment rectangle where

  alignment : Vec Alignment _
  alignment = Vec≤.padRight Left
            $ Vec≤.≤-cast (ℕₚ.m⊓n≤m _ _)
            $ Vec≤.take _ (Vec≤.fromList a)

  rectangle : Vec (Vec String _) _
  rectangle = Vec.fromList
            $ map (Vec≤.padRight "")
            $ proj₂
            $ Vec≤.rectangle
            $ map (λ row → -, Vec≤.fromList row) rows
