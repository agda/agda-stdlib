------------------------------------------------------------------------
-- The Agda standard library
--
-- Printf
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Text.Printf where

open import Level using (0ℓ)
open import Data.List.Base as List
open import Data.String.Base

import Data.Char.Base as Cₛ
import Data.Integer   as ℤₛ
import Data.Float     as Fₛ
import Data.Nat.Show  as ℕₛ

open import Data.Product
open import Data.Product.Nary.NonDependent
open import Function.Nary.NonDependent
open import Function

open import Text.Format

assemble : ∀ fmt → Product⊤ _ ⟦ fmt ⟧ → List String
assemble []              vs       = []
assemble (`ℕ      ∷ fmt) (n , vs) = ℕₛ.show n  ∷ assemble fmt vs
assemble (`ℤ      ∷ fmt) (z , vs) = ℤₛ.show z  ∷ assemble fmt vs
assemble (`Float  ∷ fmt) (f , vs) = Fₛ.show f  ∷ assemble fmt vs
assemble (`Char   ∷ fmt) (c , vs) = fromChar c ∷ assemble fmt vs
assemble (`String ∷ fmt) (s , vs) = s          ∷ assemble fmt vs
assemble (Raw str ∷ fmt) vs       = str ∷ assemble fmt vs

module _ (fmt : Format) where

  private
--    cs  = toList str
--    fmt = format cs
    n   = size fmt

  Printf : Set (⨆ n 0ℓs)
  Printf = Arrows n ⟦ fmt ⟧ (List String)

  printf : Printf
  printf = curryₙ n (assemble fmt ∘′ toProduct⊤ n)
