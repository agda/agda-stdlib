------------------------------------------------------------------------
-- The Agda standard library
--
-- Costrings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Codata.Musical.Costring where

open import Codata.Musical.Colist as Colist using (Colist)
open import Data.Char using (Char)
open import Data.String as String using (String)
open import Function using (_∘_)

-- Possibly infinite strings.

Costring : Set
Costring = Colist Char

-- Methods

toCostring : String → Costring
toCostring = Colist.fromList ∘ String.toList
