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
       ∀[ Vec A  ⇒ f ⊢ Vec≤ A ] →
       ∀[ Vec≤ A ⇒ f ⊢ Vec≤ A ]
lift incr f (as , p) = ≤-cast (incr p) (f as)

lift′ : ∀[ Vec A  ⇒ Vec≤ A ] →
        ∀[ Vec≤ A ⇒ Vec≤ A ]
lift′ = lift id

------------------------------------------------------------------------
-- Additional operations

module _ {P : A → Set p} (P? : Decidable P) where

  filter : ∀[ Vec≤ A ⇒ Vec≤ A ]
  filter = lift′ (Vec.filter P?)

  takeWhile : ∀[ Vec≤ A ⇒ Vec≤ A ]
  takeWhile = lift′ (Vec.takeWhile P?)

  dropWhile : ∀[ Vec≤ A ⇒ Vec≤ A ]
  dropWhile = lift′ (Vec.dropWhile P?)
