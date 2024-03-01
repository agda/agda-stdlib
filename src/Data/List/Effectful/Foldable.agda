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
open import Effect.Foldable
open import Function.Base
open import Level
import Relation.Binary.PropositionalEquality as ≡


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

  open Monoid M renaming (rawMonoid to M₀)

  ++-foldMap : ∀ xs {ys} →
               foldMap M₀ f (xs ++ ys) ≈ foldMap M₀ f xs ∙ foldMap M₀ f ys
  ++-foldMap []       = sym (identityˡ _)
  ++-foldMap (x ∷ xs) = trans
    (∙-congˡ (++-foldMap xs))
    (sym (assoc _ _ _))

  foldMap-morphism : IsMonoidHomomorphism (++-[]-rawMonoid A) M₀ (foldMap M₀ f)
  foldMap-morphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record
        { cong = reflexive ∘ ≡.cong (foldMap M₀ f) }
      ; homo = λ xs _ → ++-foldMap xs
      }
    ; ε-homo = refl
    }
