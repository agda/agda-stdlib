------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- `Effect.Monad.State` instead.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Category.Monad.State where

open import Effect.Monad.State public

{-# WARNING_ON_IMPORT
"Category.Monad.State was deprecated in v2.0.
Use Effect.Monad.State instead."
#-}
