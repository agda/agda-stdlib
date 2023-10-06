------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- `Effect.Comonad` instead.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Category.Comonad where

open import Effect.Comonad public

{-# WARNING_ON_IMPORT
"Category.Comonad was deprecated in v2.0.
Use Effect.Comonad instead."
#-}
