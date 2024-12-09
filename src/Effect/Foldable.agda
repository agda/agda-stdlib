------------------------------------------------------------------------
-- The Agda standard library
--
-- Foldable functors
------------------------------------------------------------------------

-- Note that currently the Foldable laws are not included here.

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Foldable where

open import Algebra.Bundles.Raw using (RawMonoid)
open import Algebra.Bundles using (Monoid)
import Algebra.Construct.Flip.Op as Op

open import Data.List.Base as List using (List; [_]; _++_)

open import Effect.Functor as Fun using (RawFunctor)

open import Function.Base using (id; flip)
open import Function.Endo.Propositional using (∘-id-monoid)
open import Level using (Level; Setω)
open import Relation.Binary.Bundles using (Setoid)

private
  variable
    f g c ℓ : Level
    A : Set f
    C : Set c


------------------------------------------------------------------------
-- The type of raw Foldables:
-- all fields can be given non-default implementations

record RawFoldable (F : Set f → Set g) : Setω where
  field
    foldMap : (M : RawMonoid c ℓ) (open RawMonoid M) →
              (A → Carrier) → F A → Carrier

  fold : (M : RawMonoid f ℓ) (open RawMonoid M) → F Carrier → Carrier
  fold M = foldMap M id

  field
    foldr : (A -> C -> C) -> C -> F A -> C
    foldl : (C -> A -> C) -> C -> F A -> C
    toList : F A → List A


------------------------------------------------------------------------
-- The type of raw Foldables, with default implementations a la haskell

record RawFoldableWithDefaults (F : Set f → Set g) : Setω where
  field
    foldMap : (M : RawMonoid c ℓ) (open RawMonoid M) →
              (A → Carrier) → F A → Carrier

  foldr : (A -> C -> C) -> C -> F A -> C
  foldr {C = C} f z t = foldMap M₀ f t z
    where M = ∘-id-monoid C ; M₀ = Monoid.rawMonoid M

  foldl : (C -> A -> C) -> C -> F A -> C
  foldl {C = C} f z t = foldMap M₀ (flip f) t z
    where M = Op.monoid (∘-id-monoid C) ; M₀ = Monoid.rawMonoid M

  toList : F A → List A
  toList {A = A} = foldMap (List.++-[]-rawMonoid A) [_]

  rawFoldable : RawFoldable F
  rawFoldable = record
    { foldMap = foldMap
    ; foldr = foldr
    ; foldl = foldl
    ; toList = toList
    }

