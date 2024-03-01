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

  open Monoid M

  private
    h = foldMap rawMonoid f

  ++-foldMap : ∀ xs {ys} → h (xs ++ ys) ≈ h xs ∙ h ys
  ++-foldMap []       = sym (identityˡ _)
  ++-foldMap (x ∷ xs) = trans (∙-congˡ (++-foldMap xs)) (sym (assoc _ _ _))

  foldMap-morphism : IsMonoidHomomorphism (++-[]-rawMonoid A) rawMonoid h
  foldMap-morphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record
        { cong = reflexive ∘ ≡.cong h }
      ; homo = λ xs _ → ++-foldMap xs
      }
    ; ε-homo = refl
    }
