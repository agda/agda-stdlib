------------------------------------------------------------------------
-- The Agda standard library
--
-- List is Foldable
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Effectful.Foldable where

open import Algebra.Bundles using (Monoid)
open import Algebra.Bundles.Raw using (RawMonoid)
open import Algebra.Morphism.Structures using (IsMonoidHomomorphism)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Effect.Foldable using (RawFoldableWithDefaults; RawFoldable)
open import Function.Base using (_∘_; id)
open import Level using (Level)
import Relation.Binary.PropositionalEquality.Core as ≡

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
-- Basic implementation using supplied defaults

foldableWithDefaults : RawFoldableWithDefaults (List {a})
foldableWithDefaults = record { foldMap = λ M → foldMap M }

------------------------------------------------------------------------
-- Specialised version using optimised implementations

foldable : RawFoldable (List {a})
foldable = record
  { foldMap = λ M → foldMap M
  ; foldr = List.foldr
  ; foldl = List.foldl
  ; toList = id
  }

------------------------------------------------------------------------
-- Properties

module _ (M : Monoid c ℓ) (f : A → Monoid.Carrier M) where

  open Monoid M

  private
    h = foldMap rawMonoid f

  []-homo : h [] ≈ ε
  []-homo = refl

  ++-homo : ∀ xs {ys} → h (xs ++ ys) ≈ h xs ∙ h ys
  ++-homo []       = sym (identityˡ _)
  ++-homo (x ∷ xs) = trans (∙-congˡ (++-homo xs)) (sym (assoc _ _ _))

  foldMap-morphism : IsMonoidHomomorphism (List.++-[]-rawMonoid A) rawMonoid h
  foldMap-morphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record
        { cong = reflexive ∘ ≡.cong h }
      ; homo = λ xs _ → ++-homo xs
      }
    ; ε-homo = []-homo
    }
