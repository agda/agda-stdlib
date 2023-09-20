------------------------------------------------------------------------
-- The Agda standard library
--
-- Dependent product combinators for setoid equality preserving
-- functions
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Product.Function.Dependent.Setoid.WithK where

open import Data.Product.Function.Dependent.Setoid public
  using (inverse)

{-# WARNING_ON_IMPORT
"Data.Product.Function.Dependent.Setoid.WithK was deprecated in v2.0.
Use Data.Product.Function.Dependent.Setoid instead."
#-}
