------------------------------------------------------------------------
-- The Agda standard library
--
-- Bounded vectors
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Bounded where

open import Level using (Level)
open import Data.Nat.Base using (_≤_)
open import Data.Vec.Base using (Vec)
import Data.Vec as Vec using (filter; takeWhile; dropWhile)
open import Function.Base using (id)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Unary using (Pred; Decidable)

private
  variable
    a p : Level
    A : Set a

------------------------------------------------------------------------
-- Publicly re-export the contents of the base module

open import Data.Vec.Bounded.Base public

------------------------------------------------------------------------
-- Additional operations

lift : ∀ {f} → f Preserves _≤_ ⟶ _≤_ →
       (∀ {n} → Vec A n  → Vec≤ A (f n)) →
       ∀ {n} →  Vec≤ A n → Vec≤ A (f n)
lift incr f (as , p) = ≤-cast (incr p) (f as)

lift′ : (∀ {n} → Vec A n  → Vec≤ A n) →
        (∀ {n} → Vec≤ A n → Vec≤ A n)
lift′ = lift id

------------------------------------------------------------------------
-- Additional operations

module _ {P : Pred A p} (P? : Decidable P) where

  filter : ∀ {n} → Vec≤ A n → Vec≤ A n
  filter = lift′ (Vec.filter P?)

  takeWhile : ∀ {n} → Vec≤ A n → Vec≤ A n
  takeWhile = lift′ (Vec.takeWhile P?)

  dropWhile : ∀ {n} → Vec≤ A n → Vec≤ A n
  dropWhile = lift′ (Vec.dropWhile P?)
