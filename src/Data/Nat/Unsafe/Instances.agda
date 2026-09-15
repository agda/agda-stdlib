------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe instances for Nat
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}

module Data.Nat.Unsafe.Instances where

open import Data.Nat.Base
open import Data.Nat.Show using (show)
open import Text.Pretty 80

instance
  open Pretty {{...}}
  ℕPretty : Pretty ℕ
  ℕPretty .pPrintPrec prec n = text (show n)
