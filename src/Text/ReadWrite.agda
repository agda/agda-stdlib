------------------------------------------------------------------------
-- The Agda standard library
--
-- ReadWrite class
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe  #-}

module Text.ReadWrite where

-- should builtin be used?
open import Agda.Builtin.Reflection using (Precedence) public
open import Data.Char.Base using (Char) public
open import Data.List.Base using (List; []; _++_; _∷_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Maybe.Base using (just)
open import Data.String.Base using (String) public
open import Data.String.Base using (fromList; toList)
open import Function.Base using (_∘_; const; _$_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Text.Write using (Write)
open import Text.Read using (Read)

private
  variable
    a : Level
    A : Set a

record ReadWrite (A : Set a) :  Set a where
  open Read
  open Write

  field
    reader : Read A
    writer : Write A

    readWrite : ∀ {x : A} → read reader (write writer x) ≡ (just x)
    writeRead : ∀ {x : A} {s : String} → (read reader s) ≡ (just x) → writeMaybe writer (read reader s) ≡ s

