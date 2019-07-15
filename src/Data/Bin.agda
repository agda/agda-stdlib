------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations and proofs for binary represented natural numbers.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bin where

open import Data.Bin.Base public
open import Data.Bin.Properties public
  using (_≟_)
open import Data.Bin.Ordering public
