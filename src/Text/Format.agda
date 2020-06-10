------------------------------------------------------------------------
-- The Agda standard library
--
-- Format strings for Printf and Scanf
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Text.Format where

open import Data.Maybe.Base

-- Formatted types
open import Data.Char.Base
open import Data.Integer.Base
open import Data.Float
open import Data.Nat.Base
open import Data.String.Base

------------------------------------------------------------------------
-- Basic types

data ArgChunk : Set where
  ℕArg ℤArg FloatArg CharArg StringArg : ArgChunk

------------------------------------------------------------------------
-- Semantics

Arg⟦_⟧ : (fmt : ArgChunk) → Set
Arg⟦ ℕArg      ⟧ = ℕ
Arg⟦ ℤArg      ⟧ = ℤ
Arg⟦ FloatArg  ⟧ = Float
Arg⟦ CharArg   ⟧ = Char
Arg⟦ StringArg ⟧ = String

lexArg : Char → Maybe ArgChunk
lexArg 'd' = just ℤArg
lexArg 'i' = just ℤArg
lexArg 'u' = just ℕArg
lexArg 'f' = just FloatArg
lexArg 'c' = just CharArg
lexArg 's' = just StringArg
lexArg _   = nothing

open import Text.Format.Generic ArgChunk lexArg Arg⟦_⟧ public

pattern `ℕ      = Arg ℕArg
pattern `ℤ      = Arg ℤArg
pattern `Float  = Arg FloatArg
pattern `Char   = Arg CharArg
pattern `String = Arg StringArg
