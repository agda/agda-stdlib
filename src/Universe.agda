------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use `Data.Universe` instead.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Universe where

{-# WARNING_ON_IMPORT
"Universe was deprecated in v1.1.
Use Data.Universe instead."
#-}

open import Data.Universe public
open import Data.Universe.Indexed public
  renaming (IndexedUniverse to Indexed-universe)
