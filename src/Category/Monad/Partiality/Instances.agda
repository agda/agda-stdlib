------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for _⊥
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe --guardedness #-}

module Category.Monad.Partiality.Instances where

open import Category.Monad.Partiality

instance
  partialityMonad = monad
