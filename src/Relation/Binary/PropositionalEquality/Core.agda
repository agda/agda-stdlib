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
    A B C : Set a

------------------------------------------------------------------------
-- Propositional equality

open import Agda.Builtin.Equality public

infix 4 _≢_
_≢_ : {A : Set a} → Rel A a
x ≢ y = ¬ x ≡ y

------------------------------------------------------------------------
-- A variant of `refl` where the argument is explicit

pattern erefl x = refl {x = x}

------------------------------------------------------------------------
-- Congruence lemmas

cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong′ : ∀ {f : A → B} x → f x ≡ f x
cong′ _ = refl

icong : ∀ {f : A → B} {x y} → x ≡ y → f x ≡ f y
icong = cong _

icong′ : ∀ {f : A → B} x → f x ≡ f x
icong′ _ = refl

cong₂ : ∀ (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

cong-app : ∀ {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
           f ≡ g → (x : A) → f x ≡ g x
cong-app refl x = refl

------------------------------------------------------------------------
-- Properties of _≡_

sym : Symmetric {A = A} _≡_
sym refl = refl

trans : Transitive {A = A} _≡_
trans refl eq = eq

subst : Substitutive {A = A} _≡_ ℓ
subst P refl p = p

subst₂ : ∀ (_∼_ : REL A B ℓ) {x y u v} → x ≡ y → u ≡ v → x ∼ u → y ∼ v
subst₂ _ refl refl p = p

resp : ∀ (P : A → Set ℓ) → P Respects _≡_
resp P refl p = p

respˡ : ∀ (∼ : Rel A ℓ) → ∼ Respectsˡ _≡_
respˡ _∼_ refl x∼y = x∼y

respʳ : ∀ (∼ : Rel A ℓ) → ∼ Respectsʳ _≡_
respʳ _∼_ refl x∼y = x∼y

resp₂ : ∀ (∼ : Rel A ℓ) → ∼ Respects₂ _≡_
resp₂ _∼_ = respʳ _∼_ , respˡ _∼_

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
