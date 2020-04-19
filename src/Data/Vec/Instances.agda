------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for Vec
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Instances where

open import Data.Vec.Categorical

instance
  vecFunctor = functor
  vecApplicative = applicative
