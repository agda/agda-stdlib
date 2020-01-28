------------------------------------------------------------------------
-- The Agda standard library
--
-- Strings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.String where

open import Data.Vec.Base as Vec using (Vec)
open import Data.Char as Char using (Char)
open import Function.Base

------------------------------------------------------------------------
-- Re-export contents of base, and decidability of equality

open import Data.String.Base public
open import Data.String.Properties using (_≈?_; _≟_; _<?_; _==_) public

------------------------------------------------------------------------
-- Operations

toVec : (s : String) → Vec Char (length s)
toVec s = Vec.fromList (toList s)

fromVec : ∀ {n} → Vec Char n → String
fromVec = fromList ∘ Vec.toList
