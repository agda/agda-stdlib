------------------------------------------------------------------------
-- The Agda standard library
--
-- Format strings for Printf and Scanf
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Char.Base using (Char)
open import Data.Maybe.Base using (Maybe)

module Text.Format.Generic where

open import Level using (0ℓ)
open import Category.Applicative
open import Data.List.Base as List
open import Data.Maybe as Maybe
open import Data.Nat.Base
open import Data.Product
open import Data.Product.Nary.NonDependent
open import Data.Sum.Base
open import Data.String.Base
import Data.Sum.Categorical.Left as Sumₗ
open import Function
open import Function.Nary.NonDependent using (0ℓs; Sets)
open import Strict

------------------------------------------------------------------------
-- Format specifications.
-- Defines the supported %-codes.

record FormatSpec : Set₁ where
  field
    ArgChunk : Set
    ArgType  : ArgChunk → Set
    lexArg   : Char → Maybe ArgChunk

module _ where
  open FormatSpec

  -- Left-biased union of format specs.
  unionSpec : FormatSpec → FormatSpec → FormatSpec
  unionSpec spec₁ spec₂ .ArgChunk  = spec₁ .ArgChunk ⊎ spec₂ .ArgChunk
  unionSpec spec₁ spec₂ .ArgType (inj₁ a) = spec₁ .ArgType a
  unionSpec spec₁ spec₂ .ArgType (inj₂ a) = spec₂ .ArgType a
  unionSpec spec₁ spec₂ .lexArg  c =
    Maybe.map inj₁ (spec₁ .lexArg c) <∣>
    Maybe.map inj₂ (spec₂ .lexArg c)

module Format (spec : FormatSpec) where

  open FormatSpec spec

  ------------------------------------------------------------------------
  -- Basic types

  data Chunk : Set where
    Arg : ArgChunk → Chunk
    Raw : String → Chunk

  Format : Set
  Format = List Chunk

  ------------------------------------------------------------------------
  -- Semantics

  size : Format → ℕ
  size = List.sum ∘′ List.map λ { (Raw _) → 0; _ → 1 }

  -- Meaning of a format as a list of value types

  ⟦_⟧ : (fmt : Format) → Sets (size fmt) 0ℓs
  ⟦ []          ⟧ = _
  ⟦ Arg a  ∷ cs ⟧ = ArgType a , ⟦ cs ⟧
  ⟦ Raw _  ∷ cs ⟧ =             ⟦ cs ⟧

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
    type bef (c ∷ cs) = _∷_ <$> chunk c ⊛ loop [] (c ∷ bef) cs where

      chunk : Char → Error ⊎ Chunk
      chunk c =
        case lexArg c of λ where
          (just ch) → pure (Arg ch)
          nothing   →
            force′ (toRevString bef) λ prefix →
            force′ (fromList cs)     λ suffix →
            inj₁ (InvalidType prefix c suffix)
