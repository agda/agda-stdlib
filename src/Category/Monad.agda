------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- `Effect.Monad` instead.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Category.Monad where

open import Effect.Monad public

{-# WARNING_ON_IMPORT
"Category.Monad was deprecated in v2.0.
Use Effect.Monad instead."
#-}
