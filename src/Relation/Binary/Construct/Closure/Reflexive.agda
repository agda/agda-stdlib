------------------------------------------------------------------------
-- The Agda standard library
--
-- Reflexive closures
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Construct.Closure.Reflexive where

open import Data.Unit
open import Level
open import Function
open import Relation.Binary
open import Relation.Binary.Construct.Constant using (Const)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A B : Set a

------------------------------------------------------------------------
-- Definition

data ReflClosure {A : Set a} (_∼_ : Rel A ℓ) : Rel A (a ⊔ ℓ) where
  refl : Reflexive (ReflClosure _∼_)
  [_]  : ∀ {x y} (x∼y : x ∼ y) → ReflClosure _∼_ x y

------------------------------------------------------------------------
-- Operations

map : ∀ {R : Rel A ℓ₁} {S : Rel B ℓ₂} {f : A → B} →
      R =[ f ]⇒ S → ReflClosure R =[ f ]⇒ ReflClosure S
map R⇒S [ xRy ] = [ R⇒S xRy ]
map R⇒S refl    = refl

------------------------------------------------------------------------
-- Properties

-- The reflexive closure has no effect on reflexive relations.
drop-refl : {R : Rel A ℓ} → Reflexive R → ReflClosure R ⇒ R
drop-refl rfl [ xRy ] = xRy
drop-refl rfl refl    = rfl

[]-injective : {R : Rel A ℓ} → ∀ {x y p q} →
               (ReflClosure R x y ∋ [ p ]) ≡ [ q ] → p ≡ q
[]-injective refl = refl

------------------------------------------------------------------------
-- Example usage

private
  module Maybe where
    Maybe : Set a → Set a
    Maybe A = ReflClosure (Const A) tt tt

    nothing : Maybe A
    nothing = refl

    just : A → Maybe A
    just = [_]



------------------------------------------------------------------------
-- Deprecations
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- v1.5

Refl = ReflClosure
{-# WARNING_ON_USAGE Refl
"Warning: Refl was deprecated in v1.5.
Please use ReflClosure instead."
#-}

