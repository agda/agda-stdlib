------------------------------------------------------------------------
-- The Agda standard library
--
-- Vec is Foldable
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Effectful.Foldable where

open import Algebra.Bundles.Raw using (RawMonoid)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (Vec; []; _∷_; foldr′; foldl′; toList)
open import Effect.Foldable using (RawFoldableWithDefaults; RawFoldable)
open import Function.Base using (id)
open import Level using (Level)

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
-- Basic implementation using supplied defaults

foldableWithDefaults : RawFoldableWithDefaults {a} (λ A → Vec A n)
foldableWithDefaults = record { foldMap = λ M → foldMap M }

------------------------------------------------------------------------
-- Specialised version using optimised implementations

foldable : RawFoldable {a} (λ A → Vec A n)
foldable = record
  { foldMap = λ M → foldMap M
  ; foldr = foldr′
  ; foldl = foldl′
  ; toList = toList
  }

