------------------------------------------------------------------------
-- The Agda standard library
--
-- The Foldable instance of List
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Effectful/Foldable where

open import Algebra.Bundles.Raw using (RawMonoid)
open import Data.List.Base
open import Data.List.Properties
open import Effect.Foldable
open import Function.Base
open import Level
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≢_; _≗_; refl; module ≡-Reasoning)

private
  variable
    a c ℓ : Level
    A : Set a


------------------------------------------------------------------------
-- Root implementation

module _ (M : RawMonoid c ℓ) where

  open RawMonoid M

  foldMap : (A → Carrier) → List A → Carrier
  foldMap f []       = ε
  foldMap f (x ∷ xs) = f x ∙ foldMap f xs

------------------------------------------------------------------------
-- Basic instance: using supplied defaults

foldableWithDefaults : RawFoldableWithDefaults (List {a})
foldableWithDefaults = record { foldMap = λ M → foldMap M }

------------------------------------------------------------------------
-- Specialised instance: using optimised implementations

foldable : RawFoldable (List {a})
foldable = record
  { foldMap = λ M → foldMap M
  ; foldr = foldr
  ; foldl = foldl
  ; toList = id
  }
