------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe instances for List
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}

module Data.List.Unsafe.Instances where

open import Data.List.Base
open import Data.Nat.Base
open import Data.Nat.Instances
open import Level using (Level)
open import Text.Write
open import Text.Pretty 80

private
  variable
    a : Level
    A : Set a

open Pretty {{...}}

instance
  ListPretty : {{ Pretty A }} → Pretty (List A)
  ListPretty .pPrintPrec prec xs = parens (commaSep (map (pPrintPrec prec) xs))
