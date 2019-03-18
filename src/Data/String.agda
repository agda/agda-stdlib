------------------------------------------------------------------------
-- The Agda standard library
--
-- Strings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.String where

open import Data.Vec as Vec using (Vec)
open import Data.Char as Char using (Char)

------------------------------------------------------------------------
-- Re-export contents of base, and decidability of equality

open import Data.String.Base public
open import Data.String.Properties using (_≟_; _==_) public

------------------------------------------------------------------------
-- Operations

toVec : (s : String) → Vec Char (length s)
toVec s = Vec.fromList (toList s)
