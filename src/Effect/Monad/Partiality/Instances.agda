------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for _⊥
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --guardedness #-}

module Effect.Monad.Partiality.Instances where

open import Effect.Monad.Partiality

instance
  partialityMonad = monad
