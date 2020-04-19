------------------------------------------------------------------------
-- The Agda standard library
--
-- Fancy display functions for Vec-based tables
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Text.Tabular.Vec where

open import Data.List.Base using (List)
open import Data.Product as Prod using (uncurry)
open import Data.String.Base using (String; rectangle; fromAlignment)
open import Data.Vec.Base
open import Function.Base

open import Text.Tabular.Base

display : ∀ {m n} → TabularConfig → Vec Alignment n → Vec (Vec String n) m →
          List String
display c a = unsafeDisplay c
            ∘ toList
            ∘ map toList
            ∘ transpose
            ∘ map (uncurry rectangle ∘ unzip)
            ∘ transpose
            ∘ map (zip (map fromAlignment a))
