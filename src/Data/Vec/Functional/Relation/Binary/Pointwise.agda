------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of relations over Vector
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Functional.Relation.Binary.Pointwise where

open import Data.Fin.Base
open import Data.Nat.Base
open import Data.Vec.Functional as VF hiding (map)
open import Level using (Level)
open import Relation.Binary

private
  variable
    a b r s ℓ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definition

Pointwise : REL A B ℓ → ∀ {n} → Vector A n → Vector B n → Set ℓ
Pointwise R xs ys = ∀ i → R (xs i) (ys i)

------------------------------------------------------------------------
-- Operations

module _ {R : REL A B r} {S : REL A B s} where

  map : R ⇒ S → ∀ {n} → Pointwise R ⇒ Pointwise S {n = n}
  map f rs i = f (rs i)
