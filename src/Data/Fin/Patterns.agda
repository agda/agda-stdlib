------------------------------------------------------------------------
-- The Agda standard library
--
-- Patterns for Fin
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Patterns where

open import Data.Fin.Base

------------------------------------------------------------------------
-- Constants

pattern 0F = zero
pattern 1F = suc 0F
pattern 2F = suc 1F
pattern 3F = suc 2F
pattern 4F = suc 3F
pattern 5F = suc 4F
pattern 6F = suc 5F
pattern 7F = suc 6F
pattern 8F = suc 7F
pattern 9F = suc 8F
