------------------------------------------------------------------------
-- The Agda standard library
--
-- Format strings for Printf and Scanf
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Text.Format where

open import Data.Maybe.Base
open import Text.Format.Generic

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

ArgType : (fmt : ArgChunk) → Set
ArgType ℕArg      = ℕ
ArgType ℤArg      = ℤ
ArgType FloatArg  = Float
ArgType CharArg   = Char
ArgType StringArg = String

lexArg : Char → Maybe ArgChunk
lexArg 'd' = just ℤArg
lexArg 'i' = just ℤArg
lexArg 'u' = just ℕArg
lexArg 'f' = just FloatArg
lexArg 'c' = just CharArg
lexArg 's' = just StringArg
lexArg _   = nothing

formatSpec : FormatSpec
formatSpec .FormatSpec.ArgChunk = ArgChunk
formatSpec .FormatSpec.ArgType  = ArgType
formatSpec .FormatSpec.lexArg   = lexArg

open Format formatSpec public

pattern `ℕ      = Arg ℕArg
pattern `ℤ      = Arg ℤArg
pattern `Float  = Arg FloatArg
pattern `Char   = Arg CharArg
pattern `String = Arg StringArg
