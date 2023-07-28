------------------------------------------------------------------------
-- The Agda standard library
--
-- A non-empty fresh list
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Fresh.NonEmpty where

open import Level using (Level; _⊔_)
open import Data.List.Fresh as List# using (List#; []; cons; fresh)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.Core using (Rel)

private
  variable
    a r : Level
    A : Set a
    R : Rel A r

------------------------------------------------------------------------
-- Definition

infixr 5 _∷#⁺_

record List#⁺ (A : Set a) (R : Rel A r) : Set (a ⊔ r) where
  constructor _∷#⁺_
  field
    head : A
    tail : List# A R
    {rel} : fresh A R head tail

open List#⁺

------------------------------------------------------------------------
-- Operations

uncons : List#⁺ A R → A × List# A R
uncons (x ∷#⁺ xs) = x , xs

[_] : A → List#⁺ A R
[ x ] = x ∷#⁺ []

length : List#⁺ A R → ℕ
length (x ∷#⁺ xs) = suc (List#.length xs)

-- Conversion

toList# : List#⁺ A R → List# A R
toList# l = cons (l .head) (l .tail) (l .rel)

fromList# : List# A R → Maybe (List#⁺ A R)
fromList# []             = nothing
fromList# (cons a as ps) = just (record { head = a ; tail = as ; rel = ps })
