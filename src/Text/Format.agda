------------------------------------------------------------------------
-- The Agda standard library
--
-- Format strings for Printf and Scanf
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Text.Format where

open import Level using (0ℓ)
open import Category.Applicative
open import Data.List.Base as List
open import Data.Product
open import Data.Product.Nary.NonDependent
open import Data.Sum.Base
import Data.Sum.Categorical.Left as Sumₗ
open import Function
open import Function.Nary.NonDependent using (0ℓs; Sets)

-- Formatted types
open import Data.Char.Base
open import Data.Integer.Base
open import Data.Float
open import Data.Nat.Base
open import Data.String.Base

------------------------------------------------------------------------
-- Basic types

data Chunk : Set where
  `ℕ `ℤ `Float `Char `String : Chunk
  Raw : String → Chunk

Format : Set
Format = List Chunk

------------------------------------------------------------------------
-- Semantics

size : Format → ℕ
size = List.sum ∘′ List.map λ { (Raw _) → 0; _ → 1 }

-- Meaning of a format as a list of value types

⟦_⟧ : (fmt : Format) → Sets (size fmt) 0ℓs
⟦ []           ⟧ = _
⟦ `ℕ      ∷ cs ⟧ = ℕ      , ⟦ cs ⟧
⟦ `ℤ      ∷ cs ⟧ = ℤ      , ⟦ cs ⟧
⟦ `Float  ∷ cs ⟧ = Float  , ⟦ cs ⟧
⟦ `Char   ∷ cs ⟧ = Char   , ⟦ cs ⟧
⟦ `String ∷ cs ⟧ = String , ⟦ cs ⟧
⟦ Raw _   ∷ cs ⟧ =          ⟦ cs ⟧

------------------------------------------------------------------------
-- Lexer: from Strings to Formats

-- Lexing may fail. To have a useful error message, we defined the following
-- enumerated type

data Error : Set where
  UnexpectedEndOfString : String → Error
  -- ^ expected a type declaration; found an empty string
  InvalidType : String → Char → String → Error
  -- ^ invalid type declaration
  --   return a focus: prefix processed, character causing failure, rest

lexer : String → Error ⊎ List Chunk
lexer input = loop [] [] (toList input) where

  open RawApplicative (Sumₗ.applicative Error 0ℓ)

  -- Type synonyms used locally to document the code
  RevWord = List Char -- Mere characters accumulated so far
  Prefix  = RevWord   -- Prefix of the input String already read

  toRevString : RevWord → String
  toRevString = fromList ∘′ reverse

  -- Push a Raw token if we have accumulated some mere characters
  push : RevWord → List Chunk → List Chunk
  push [] ks = ks
  push cs ks = Raw (toRevString cs) ∷ ks

  -- Main loop
  loop : RevWord → Prefix → List Char → Error ⊎ List Chunk
  type :           Prefix → List Char → Error ⊎ List Chunk

  loop acc bef []               = pure (push acc [])
  -- escaped '%' character: treat like a mere character
  loop acc bef ('%' ∷ '%' ∷ cs) = loop ('%' ∷ acc) ('%' ∷ '%' ∷ bef) cs
  -- non escaped '%': type declaration following
  loop acc bef ('%' ∷ cs)       = push acc <$> type ('%' ∷ bef) cs
  -- mere character: push onto the accumulator
  loop acc bef (c ∷ cs)         = loop (c ∷ acc) (c ∷ bef) cs

  type bef []       = inj₁ (UnexpectedEndOfString input)
  type bef (c ∷ cs) = (λ ck → _∷_ <$> ck ⊛ loop [] (c ∷ bef) cs) $
    case c of λ where
      'd' → pure `ℤ
      'i' → pure `ℤ
      'u' → pure `ℕ
      'f' → pure `Float
      'c' → pure `Char
      's' → pure `String
      _   → inj₁ (InvalidType (toRevString bef) c (fromList cs))
