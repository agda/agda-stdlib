------------------------------------------------------------------------
-- The Agda standard library
--
-- The Foldable instance of List
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Effectful.Foldable where

open import Algebra.Bundles using (Monoid)
open import Algebra.Bundles.Raw using (RawMonoid)
open import Algebra.Morphism.Structures using (IsMonoidHomomorphism)
open import Data.List.Base
open import Data.List.Properties
open import Effect.Foldable
open import Function.Base
open import Level
import Relation.Binary.PropositionalEquality as ≡
--  using (_≡_; _≢_; _≗_; refl; module ≡-Reasoning)

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

------------------------------------------------------------------------
-- Properties

module _ (M : Monoid c ℓ) (f : A → Monoid.Carrier M) where

  open Monoid M using (_∙_; _≈_; identityˡ; ∙-congˡ)
    renaming (rawMonoid to M₀)

  ++-foldMap : ∀ xs {ys} →
               foldMap M₀ f (xs ++ ys) ≈ foldMap M₀ f xs ∙ foldMap M₀ f ys
  ++-foldMap []       = Monoid.sym M (identityˡ _)
  ++-foldMap (x ∷ xs) = Monoid.trans M
    (∙-congˡ (++-foldMap xs))
    (Monoid.sym M (Monoid.assoc M _ _ _))

  foldMap-morphism : IsMonoidHomomorphism (++-[]-rawMonoid A) M₀ (foldMap M₀ f)
  foldMap-morphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record
        { cong = Monoid.reflexive M ∘ ≡.cong (foldMap M₀ f) }
      ; homo = λ xs _ → ++-foldMap xs
      }
    ; ε-homo = Monoid.refl M
    }
