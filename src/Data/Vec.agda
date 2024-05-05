------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors
------------------------------------------------------------------------

-- This implementation is designed for reasoning about dynamic
-- vectors which may increase or decrease in size.

-- See `Data.Vec.Functional` for an alternative implementation as
-- functions from finite sets, which is more suitable for reasoning
-- about fixed sized vectors and for when ease of retrieval is
-- important.

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec where

open import Level
open import Data.Bool.Base
import Data.Nat.Properties as ℕ
open import Data.Vec.Bounded.Base as Vec≤
  using (Vec≤; ≤-cast; fromVec)
open import Function.Base using (_$_)
open import Relation.Nullary
open import Relation.Unary

private
  variable
    a p : Level
    A : Set a

------------------------------------------------------------------------
-- Publicly re-export the contents of the base module

open import Data.Vec.Base public

------------------------------------------------------------------------
-- Additional operations

module _ {P : A → Set p} (P? : Decidable P) where

  filter : ∀ {n} → Vec A n → Vec≤ A n
  filter []       = Vec≤.[]
  filter (a ∷ as) = if does (P? a) then a Vec≤.∷_ else ≤-cast (ℕ.n≤1+n _) $ filter as

  takeWhile : ∀ {n} → Vec A n → Vec≤ A n
  takeWhile []       = Vec≤.[]
  takeWhile (a ∷ as) = if does (P? a) then a Vec≤.∷ takeWhile as else Vec≤.[]

  dropWhile : ∀ {n} → Vec A n → Vec≤ A n
  dropWhile Vec.[]       = Vec≤.[]
  dropWhile (a Vec.∷ as) =
    if does (P? a) then ≤-cast (ℕ.n≤1+n _) (dropWhile as)
    else fromVec (a Vec.∷ as)
