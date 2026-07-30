------------------------------------------------------------------------
-- The Agda standard library
--
-- Show class
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}

module Text.Show where

-- should builtin be used?
open import Agda.Builtin.Reflection using (Precedence)
open import Agda.Builtin.Int
open import Agda.Builtin.String using (primShowNat)
open import Data.Bool.Base using (Bool)
open import Data.Char.Base using (Char)
open import Data.List.Base using (List; []; _++_; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.String.Base using (String; fromList; toList)
open import Function.Base using (_∘_; const; _$_)
open import Level using (Level)

private
  variable
    a : Level
    A : Set a

record Show {α} (A : Set α) :  Set α
  where
  constructor show′

  field  showsPrecList :  Precedence → A → List Char → List Char

  showPrecList : Precedence → A → List Char
  showPrecList prec a =  showsPrecList prec a []

  showsPrec : Precedence → A → String → String
  showsPrec prec a str = fromList (showsPrecList prec a (toList str))

  showPrec : Precedence → A → String
  showPrec prec a = fromList (showsPrecList prec a [])

  show : A → String
  show = showPrec Precedence.unrelated

open Show {{...}}

-- NOTE: could/should be moved into respective modules, e.g. Data.List.Show
instance
  IntShow : Show Int
  IntShow .Show.showsPrecList _ i str = toList (primShowInteger i) ++ str

instance
  NatShow : Show ℕ
  NatShow .Show.showsPrecList _ n str = (toList (primShowNat n)) ++ str

instance
  ListShow : {{ Show A }} → Show (List A)
  ListShow .Show.showsPrecList prec [] str = '[' ∷ (']' ∷ str)
  ListShow .Show.showsPrecList prec (x ∷ xs) str = '[' ∷ listShow' prec x xs str
    where
      -- after the first call, don't prepend '['
      -- and don't call on [], hence head taken as its own argument
      listShow' : {{ Show A }} → Precedence → A → List A → List Char → List Char
      listShow' prec x [] str = showsPrecList prec x (']' ∷ str)
      listShow' prec x (x₁ ∷ xs) str = showsPrecList prec x (',' ∷ (listShow' prec x₁ xs str))

-- some examples to show the instances working
private
  test : String
  test = show (5 ∷ 2 ∷ [])
