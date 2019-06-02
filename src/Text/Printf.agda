------------------------------------------------------------------------
-- The Agda standard library
--
-- Printf
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Text.Printf where

open import Level using (0ℓ; Lift)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.Product
open import Data.Product.Nary.NonDependent
open import Data.String.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Function.Nary.NonDependent
open import Function
open import Strict

import Data.Char.Base as Cₛ
import Data.Integer   as ℤₛ
import Data.Float     as Fₛ
import Data.Nat.Show  as ℕₛ

open import Text.Format as Format hiding (Error)

assemble : ∀ fmt → Product⊤ _ ⟦ fmt ⟧ → List String
assemble []              vs       = []
assemble (`ℕ      ∷ fmt) (n , vs) = ℕₛ.show n  ∷ assemble fmt vs
assemble (`ℤ      ∷ fmt) (z , vs) = ℤₛ.show z  ∷ assemble fmt vs
assemble (`Float  ∷ fmt) (f , vs) = Fₛ.show f  ∷ assemble fmt vs
assemble (`Char   ∷ fmt) (c , vs) = fromChar c ∷ assemble fmt vs
assemble (`String ∷ fmt) (s , vs) = s          ∷ assemble fmt vs
assemble (Raw str ∷ fmt) vs       = str ∷ assemble fmt vs

record Error (e : Format.Error) : Set where

private

  Size : Format.Error ⊎ Format → ℕ
  Size (inj₁ err) = 0
  Size (inj₂ fmt) = size fmt

  Printf : ∀ pr → Set (⨆ (Size pr) 0ℓs)
  Printf (inj₁ err) = Error err
  Printf (inj₂ fmt) = Arrows _ ⟦ fmt ⟧ String

  printf' : ∀ pr → Printf pr
  printf' (inj₁ err) = _
  printf' (inj₂ fmt) = curry⊤ₙ _ (concat ∘′ assemble fmt)

printf : (input : String) → Printf (lexer input)
printf input = printf' (lexer input)
