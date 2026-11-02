------------------------------------------------------------------------
-- The Agda standard library
--
-- Read class
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe  #-}

module Text.Read where

open import Data.Char.Base using (Char) public
open import Data.List.Base using (List; []; _++_; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing; map)
open import Data.Product.Base using (_×_; _,_; proj₁) renaming (map to map×)
open import Data.String.Base using (String) public
open import Data.String.Base using (fromList; toList)
open import Function.Base using (_∘_; const; _$_; id)
open import Level using (Level)
open import Reflection.AST.Fixity using (Precedence)

private
  variable
    a : Level
    A : Set a

record Read (A : Set a) : Set a where
  field
    readsPrecList : Precedence → List Char → Maybe (A × List Char)

  readPrecList : Precedence → List Char → Maybe A
  readPrecList prec str = map proj₁ (readsPrecList prec str)

  readsPrec : Precedence → String → Maybe (A × String)
  readsPrec prec str = map (map× id fromList) (readsPrecList prec (toList str))

  readPrec : Precedence → String → Maybe A
  readPrec prec = (readPrecList prec) ∘ toList

  read : String → Maybe A
  read = readPrec Precedence.unrelated
