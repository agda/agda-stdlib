------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec where

open import Level
import Data.Nat.Properties as ℕₚ
open import Data.Vec.Bounded.Base as Bounded
  using (Bounded; ≤-cast; fromVec)
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

  filter : ∀[ Vec A ⇒ Bounded A ]
  filter []       = Bounded.[]
  filter (a ∷ as) with P? a
  ... | yes p = a Bounded.∷ filter as
  ... | no ¬p = ≤-cast (ℕₚ.n≤1+n _) (filter as)

  takeWhile : ∀[ Vec A ⇒ Bounded A ]
  takeWhile []       = Bounded.[]
  takeWhile (a ∷ as) with P? a
  ... | yes p = a Bounded.∷ takeWhile as
  ... | no ¬p = Bounded.[]

  dropWhile : ∀[ Vec A ⇒ Bounded A ]
  dropWhile Vec.[]       = Bounded.[]
  dropWhile (a Vec.∷ as) with P? a
  ... | yes p = ≤-cast (ℕₚ.n≤1+n _) (dropWhile as)
  ... | no ¬p = fromVec (a Vec.∷ as)
