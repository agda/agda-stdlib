------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for _⊥
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --guardedness #-}

module Category.Monad.Partiality.Instances where

open import Category.Monad.Partiality

instance
  partialityMonad = monad
