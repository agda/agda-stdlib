------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- `Effect.Monad.Reader` instead.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Category.Monad.Reader where

open import Effect.Monad.Reader public

{-# WARNING_ON_IMPORT
"Category.Monad.Reader was deprecated in v2.0.
Use Effect.Monad.Reader instead."
#-}
