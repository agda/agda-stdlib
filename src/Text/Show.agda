------------------------------------------------------------------------
-- The Agda standard library
--
-- Show class
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe  #-}

module Text.Show where

-- should builtin be used?
open import Agda.Builtin.Reflection using (Precedence) public
open import Data.Char.Base using (Char) public
open import Data.List.Base using (List; []; _++_; _∷_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String.Base using (String) public
open import Data.String.Base using (fromList; toList)
open import Function.Base using (_∘_; const; _$_)
open import Level using (Level)

private
  variable
    a : Level
    A : Set a

record Show (A : Set a) :  Set a where
  field
    showsPrecList :  Precedence → A → List Char → List Char

  showPrecList : Precedence → A → List Char
  showPrecList prec x =  showsPrecList prec x []

  showsPrec : Precedence → A → String → String
  showsPrec prec x str = fromList (showsPrecList prec x (toList str))

  showPrec : Precedence → A → String
  showPrec prec x = fromList (showsPrecList prec x [])

  show : A → String
  show = showPrec Precedence.unrelated
