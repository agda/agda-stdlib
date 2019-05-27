------------------------------------------------------------------------
-- The Agda standard library
--
-- Bounded vectors
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Bounded where

open import Level using (Level)
open import Data.Nat.Base
open import Data.Vec as Vec using (Vec)
open import Function
open import Relation.Binary using (_Preserves_⟶_)
open import Relation.Unary

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
       ∀[ Vec A     ⇒ f ⊢ Bounded A ] →
       ∀[ Bounded A ⇒ f ⊢ Bounded A ]
lift incr f (as , p) = ≤-cast (incr p) (f as)

lift′ : ∀[ Vec A     ⇒ Bounded A ] →
        ∀[ Bounded A ⇒ Bounded A ]
lift′ = lift id

------------------------------------------------------------------------
-- Additional operations

module _ {P : A → Set p} (P? : Decidable P) where

  filter : ∀[ Bounded A ⇒ Bounded A ]
  filter = lift′ (Vec.filter P?)

  takeWhile : ∀[ Bounded A ⇒ Bounded A ]
  takeWhile = lift′ (Vec.takeWhile P?)

  dropWhile : ∀[ Bounded A ⇒ Bounded A ]
  dropWhile = lift′ (Vec.dropWhile P?)
