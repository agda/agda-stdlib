------------------------------------------------------------------------
-- The Agda standard library
--
-- Propositional equality
--
-- This file contains some core definitions which are re-exported by
-- Relation.Binary.PropositionalEquality.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.PropositionalEquality.Core where

open import Data.Product.Base using (_,_)
open import Function.Base using (_∘_)
open import Level
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary.Negation.Core using (¬_)

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
-- Pointwise equality

infix 4 _≗_

_≗_ : (f g : A → B) → Set _
_≗_ {A = A} {B = B} f g = ∀ x → f x ≡ g x


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
