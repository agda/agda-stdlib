------------------------------------------------------------------------
-- The Agda standard library
--
-- Printf
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Text.Printf where

open import Level using (0ℓ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.String.Base
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (⊤)

import Data.Char.Base as Cₛ
import Data.Integer   as ℤₛ
import Data.Float     as Fₛ
import Data.Nat.Show  as ℕₛ

open import Data.Product
open import Data.Product.Nary.NonDependent
open import Function.Nary.NonDependent
open import Function

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
  field impossible : ⊥

module _ (input : String) where

  private

    constraint : Set
    constraint = case lexer input of λ where
      (inj₁ err) → Error err
      (inj₂ fmt) → ⊤

  module _ {pr : constraint} where

    private

      fmt : Format
      fmt with lexer input
      ... | inj₁ err = ⊥-elim (Error.impossible pr)
      ... | inj₂ fmt = fmt

      n   = size fmt

    Printf : Set (⨆ n 0ℓs)
    Printf = Arrows n ⟦ fmt ⟧ String

    printf : Printf
    printf = curryₙ n (concat ∘′ assemble fmt ∘′ toProduct⊤ n)
