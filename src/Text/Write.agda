------------------------------------------------------------------------
-- The Agda standard library
--
-- Write class
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe  #-}

module Text.Write where

-- should builtin be used?
open import Data.Bool.Base using (true; false)
open import Data.Char.Base using (Char) public
open import Data.List.Base using (List; []; [_]; _++_; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String.Base using (String) public
open import Data.String.Base using (fromList; toList; concat)
open import Function.Base using (_∘_; const; _$_)
open import Level using (Level)
open import Reflection.AST.Fixity using (Precedence; _≤ᵇ_; _≤_) public

private
  variable
    a : Level
    A : Set a

record Write (A : Set a) :  Set a where
  constructor mkWrite
  field
    writesPrecList :  Precedence → A → List String → List String

  writePrecList : Precedence → A → List String
  writePrecList prec x =  writesPrecList prec x []

  writesPrec : Precedence → A → String → String
  writesPrec prec x str = concat (writesPrecList prec x [ str ])

  writePrec : Precedence → A → String
  writePrec prec x = concat (writesPrecList prec x [])

  write : A → String
  write = writePrec (Precedence.related 0.0)

  writeMaybe : Maybe A → String
  writeMaybe nothing = ""
  writeMaybe (just x) = write x

------------------------------------------------------------------------
-- Utils

-- surround a string with two given characters (e.g. parentheses) if
-- the string represents the result of calling `write` on an inner
-- operator/function whose precedence is lower than or equal to
-- the calling operator/function
writeSurround : A → A → Precedence → Precedence → List A → List A
writeSurround lbrac rbrac callerPrec calleePrec str with (calleePrec ≤ᵇ callerPrec)
... | false = str
... | true = lbrac ∷ (str ++ [ rbrac ])

writeParens : Precedence → Precedence → List String → List String
writeParens = writeSurround "(" ")"
