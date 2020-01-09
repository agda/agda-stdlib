------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use `Data.Universe` instead.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Universe where

open import Data.Universe public
open import Data.Universe.Indexed public
  renaming (IndexedUniverse to Indexed-universe)
