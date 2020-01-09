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
open import Function.Base using (_∘_)
open import Level
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary using (¬_)

private
  variable
    a b ℓ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Propositional equality

open import Agda.Builtin.Equality public

infix 4 _≢_
_≢_ : {A : Set a} → Rel A a
x ≢ y = ¬ x ≡ y

------------------------------------------------------------------------
-- Properties of _≡_

sym : Symmetric {A = A} _≡_
sym refl = refl

trans : Transitive {A = A} _≡_
trans refl eq = eq

subst : Substitutive {A = A} _≡_ ℓ
subst P refl p = p

cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

respˡ : ∀ (∼ : Rel A ℓ) → ∼ Respectsˡ _≡_
respˡ _∼_ refl x∼y = x∼y

respʳ : ∀ (∼ : Rel A ℓ) → ∼ Respectsʳ _≡_
respʳ _∼_ refl x∼y = x∼y

resp₂ : ∀ (∼ : Rel A ℓ) → ∼ Respects₂ _≡_
resp₂ _∼_ = respʳ _∼_ , respˡ _∼_

------------------------------------------------------------------------
-- Various equality rearrangement lemmas

trans-reflʳ : ∀ {x y : A} (p : x ≡ y) → trans p refl ≡ p
trans-reflʳ refl = refl

trans-assoc : ∀ {x y z u : A} (p : x ≡ y) {q : y ≡ z} {r : z ≡ u} →
  trans (trans p q) r ≡ trans p (trans q r)
trans-assoc refl = refl

trans-symˡ : ∀ {x y : A} (p : x ≡ y) → trans (sym p) p ≡ refl
trans-symˡ refl = refl

trans-symʳ : ∀ {x y : A} (p : x ≡ y) → trans p (sym p) ≡ refl
trans-symʳ refl = refl

------------------------------------------------------------------------
-- Properties of _≢_

≢-sym : Symmetric {A = A} _≢_
≢-sym x≢y =  x≢y ∘ sym

------------------------------------------------------------------------
-- Convenient syntax for equational reasoning

-- This is a special instance of `Relation.Binary.Reasoning.Setoid`.
-- Rather than instantiating the latter with (setoid A), we reimplement
-- equation chains from scratch since then goals are printed much more
-- readably.

module ≡-Reasoning {A : Set a} where

  infix  3 _∎
  infixr 2 _≡⟨⟩_ step-≡ step-≡˘
  infix  1 begin_

  begin_ : ∀{x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ y≡z x≡y = trans x≡y y≡z

  step-≡˘ : ∀ (x {y z} : A) → y ≡ z → y ≡ x → x ≡ z
  step-≡˘ _ y≡z y≡x = trans (sym y≡x) y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _∎ _ = refl

  syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
  syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z
