------------------------------------------------------------------------
-- The Agda standard library
--
-- Propositional equality
--
-- This file contains some core definitions which are re-exported by
-- Relation.Binary.PropositionalEquality.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.PropositionalEquality.Core where

open import Data.Product using (_,_)
open import Level
open import Relation.Binary.Core
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Propositional equality

open import Agda.Builtin.Equality public

infix 4 _≢_
_≢_ : ∀ {a} {A : Set a} → Rel A a
x ≢ y = ¬ x ≡ y

------------------------------------------------------------------------
-- Some properties

module _ {a} {A : Set a} where

  sym : Symmetric {A = A} _≡_
  sym refl = refl

  trans : Transitive {A = A} _≡_
  trans refl eq = eq

  cong : ∀ {b} {B : Set b} (f : A → B) → f Preserves _≡_ ⟶ _≡_
  cong f refl = refl

  subst : ∀ {p} → Substitutive {A = A} _≡_ p
  subst P refl p = p

  respˡ : ∀ {ℓ} (∼ : Rel A ℓ) → ∼ Respectsˡ _≡_
  respˡ _∼_ refl x∼y = x∼y

  respʳ : ∀ {ℓ} (∼ : Rel A ℓ) → ∼ Respectsʳ _≡_
  respʳ _∼_ refl x∼y = x∼y

  resp₂ : ∀ {ℓ} (∼ : Rel A ℓ) → ∼ Respects₂ _≡_
  resp₂ _∼_ = respʳ _∼_ , respˡ _∼_

  isEquivalence : IsEquivalence {A = A} _≡_
  isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
