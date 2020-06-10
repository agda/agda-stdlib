------------------------------------------------------------------------
-- The Agda standard library
--
-- Generic printf function.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Text.Printf.Generic where

open import Level using (Level; 0ℓ; _⊔_; Lift)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Char.Base
open import Data.Maybe.Base
open import Data.Nat.Base using (ℕ)
open import Data.Product
open import Data.Product.Nary.NonDependent
open import Data.String.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Function.Nary.NonDependent
open import Function

import Text.Format.Generic as Format

record PrintfSpec {ℓ} (A : Set ℓ) : Set (Level.suc 0ℓ ⊔ ℓ) where
  field
    ArgChunk  : Set
    lexArg    : Char → Maybe ArgChunk
    ⟦_⟧Arg    : ArgChunk → Set
    renderArg : ∀ arg → ⟦ arg ⟧Arg → A
    renderStr : String → A

private
  variable
    ℓ : Level
    A B : Set ℓ

module Printf (spec : PrintfSpec A) where

  open PrintfSpec spec
  open Format ArgChunk lexArg ⟦_⟧Arg renaming (Error to FormatError)

  assemble : ∀ fmt → Product⊤ _ ⟦ fmt ⟧ → List A
  assemble [] vs                    = []
  assemble (Arg a   ∷ fmt) (x , vs) = renderArg a x ∷ assemble fmt vs
  assemble (Raw str ∷ fmt) vs       = renderStr str ∷ assemble fmt vs

  record Error (e : FormatError) : Set ℓ where

  private

    Size : FormatError ⊎ Format → ℕ
    Size (inj₁ err) = 0
    Size (inj₂ fmt) = size fmt

  Printf : ∀ pr → Set ℓ → Set (ℓ ⊔ ⨆ (Size pr) 0ℓs)
  Printf (inj₁ err) _ = Error err
  Printf (inj₂ fmt) B = Arrows _ ⟦ fmt ⟧ B

  private

    printf′ : ∀ pr → (List A → B) → Printf pr B
    printf′ (inj₁ err) _     = _
    printf′ (inj₂ fmt) smash = curry⊤ₙ _ (smash ∘′ assemble fmt)

  printf : (List A → B) → (input : String) → Printf (lexer input) B
  printf k input = printf′ (lexer input) k
