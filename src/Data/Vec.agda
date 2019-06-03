------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec where

open import Level
import Data.Nat.Properties as ℕₚ
open import Data.Vec.Bounded.Base as Vec≤
  using (Vec≤; ≤-cast; fromVec)
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
  filter (a ∷ as) with P? a
  ... | yes p = a Vec≤.∷ filter as
  ... | no ¬p = ≤-cast (ℕₚ.n≤1+n _) (filter as)

  takeWhile : ∀ {n} → Vec A n → Vec≤ A n
  takeWhile []       = Vec≤.[]
  takeWhile (a ∷ as) with P? a
  ... | yes p = a Vec≤.∷ takeWhile as
  ... | no ¬p = Vec≤.[]

  dropWhile : ∀ {n} → Vec A n → Vec≤ A n
  dropWhile Vec.[]       = Vec≤.[]
  dropWhile (a Vec.∷ as) with P? a
  ... | yes p = ≤-cast (ℕₚ.n≤1+n _) (dropWhile as)
  ... | no ¬p = fromVec (a Vec.∷ as)
