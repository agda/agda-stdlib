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
open import Data.Maybe.Base hiding (map)
open import Data.Nat.Base using (ℕ)
open import Data.Product hiding (map)
open import Data.Product.Nary.NonDependent
open import Data.String.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Function.Nary.NonDependent
open import Function

open import Text.Format.Generic

private
  variable
    ℓ : Level
    A B : Set ℓ

------------------------------------------------------------------------
-- Printf argument specifications.
-- Defines the rendering of chunks.

record PrintfSpec {ℓ} (spec : FormatSpec) (A : Set ℓ) : Set (Level.suc 0ℓ ⊔ ℓ) where

  open FormatSpec spec public

  field
    renderArg : ∀ arg → ArgType arg → A
    renderStr : String → A

module Type (spec : FormatSpec) where

  open Format spec renaming (Error to FormatError)

  record Error (e : FormatError) : Set ℓ where

  private

    Size : FormatError ⊎ Format → ℕ
    Size (inj₁ err) = 0
    Size (inj₂ fmt) = size fmt

  Printf : ∀ pr → Set ℓ → Set (ℓ ⊔ ⨆ (Size pr) 0ℓs)
  Printf (inj₁ err) _ = Error err
  Printf (inj₂ fmt) B = Arrows _ ⟦ fmt ⟧ B

  map : ∀ pr → (A → B) → Printf pr A → Printf pr B
  map (inj₁ err) f p = _
  map (inj₂ fmt) f p = mapₙ _ f p

module Render {spec : FormatSpec} (render : PrintfSpec spec A) where

  open PrintfSpec render
  open Type spec

  open Format spec renaming (Error to FormatError)

  assemble : ∀ fmt → Product⊤ _ ⟦ fmt ⟧ → List A
  assemble [] vs                    = []
  assemble (Arg a   ∷ fmt) (x , vs) = renderArg a x ∷ assemble fmt vs
  assemble (Raw str ∷ fmt) vs       = renderStr str ∷ assemble fmt vs

  private

    printf′ : ∀ pr → Printf pr (List A)
    printf′ (inj₁ err) = _
    printf′ (inj₂ fmt) = curry⊤ₙ _ (assemble fmt)

  printf : (input : String) → Printf (lexer input) (List A)
  printf input = printf′ (lexer input)
