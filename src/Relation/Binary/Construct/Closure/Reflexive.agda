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

data Refl {A : Set a} (_∼_ : Rel A ℓ) : Rel A (a ⊔ ℓ) where
  refl : Reflexive (Refl _∼_)
  [_]  : ∀ {x y} (x∼y : x ∼ y) → Refl _∼_ x y

------------------------------------------------------------------------
-- Operations

map : ∀ {_R₁_ : Rel A ℓ₁} {_R₂_ : Rel B ℓ₂} {f : A → B} →
      _R₁_ =[ f ]⇒ _R₂_ → Refl _R₁_ =[ f ]⇒ Refl _R₂_
map R₁⇒R₂ [ xRy ] = [ R₁⇒R₂ xRy ]
map R₁⇒R₂ refl    = refl

------------------------------------------------------------------------
-- Properties

-- The reflexive closure has no effect on reflexive relations.
drop-refl : {_R_ : Rel A ℓ} → Reflexive _R_ → Refl _R_ ⇒ _R_
drop-refl rfl [ x∼y ] = x∼y
drop-refl rfl refl    = rfl

[]-injective : {_∼_ : Rel A ℓ} → ∀ {x y p q} →
               (Refl _∼_ x y ∋ [ p ]) ≡ [ q ] → p ≡ q
[]-injective refl = refl

------------------------------------------------------------------------
-- Example: Maybe

module Maybe where

  Maybe : ∀ {ℓ} → Set ℓ → Set ℓ
  Maybe A = Refl (Const A) tt tt

  nothing : ∀ {a} {A : Set a} → Maybe A
  nothing = refl

  just : ∀ {a} {A : Set a} → A → Maybe A
  just = [_]
