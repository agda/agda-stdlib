------------------------------------------------------------------------
-- The Agda standard library
--
-- The Foldable instance of Vec
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Effectful.Foldable where

open import Algebra.Bundles.Raw using (RawMonoid)
open import Data.Nat.Base
open import Data.Vec.Base
open import Data.Vec.Properties
open import Effect.Foldable
open import Function.Base
open import Level
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≢_; _≗_; refl; module ≡-Reasoning)

private
  variable
    a c ℓ : Level
    A : Set a
    n : ℕ


------------------------------------------------------------------------
-- Root implementation

module _ (M : RawMonoid c ℓ) where

  open RawMonoid M

  foldMap : (A → Carrier) → Vec A n → Carrier
  foldMap f []       = ε
  foldMap f (x ∷ xs) = f x ∙ foldMap f xs

------------------------------------------------------------------------
-- Basic instance: using supplied defaults

foldableWithDefaults : RawFoldableWithDefaults {a} (λ A → Vec A n)
foldableWithDefaults = record { foldMap = λ M → foldMap M }

------------------------------------------------------------------------
-- Specialised instance: using optimised implementations

foldable : RawFoldable {a} (λ A → Vec A n)
foldable = record
  { foldMap = λ M → foldMap M
  ; foldr = foldr′
  ; foldl = foldl′
  ; toList = toList
  }

