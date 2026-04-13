------------------------------------------------------------------------
-- The Agda standard library
--
-- Costrings
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module Codata.Musical.Costring where

open import Codata.Musical.Colist.Base as Colist using (Colist)
open import Data.Char.Base using (Char)
open import Data.String.Base as String using (String)
open import Function.Base using (_∘_)

-- Possibly infinite strings.

Costring : Set
Costring = Colist Char

-- Methods

toCostring : String → Costring
toCostring = Colist.fromList ∘ String.toList
