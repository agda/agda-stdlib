------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe instances for Maybe
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}

module Data.Maybe.Unsafe.Instances where

open import Data.Maybe.Base
open import Text.Pretty 80
open import Level using (Level)

private
  variable
    a : Level
    A : Set a

instance
  open Pretty {{...}}
  MaybePretty : {{ Pretty A }} → Pretty (Maybe A)
  MaybePretty .pPrintPrec prec (just x) = (text "just") <+> pPrintPrec prec x
  MaybePretty .pPrintPrec prec nothing = text "nothing"
