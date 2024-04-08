------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the `Reflects` construct
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Reflects where

open import Agda.Builtin.Equality

open import Data.Bool.Base
open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Level using (Level)
open import Function.Base using (id; _$_; _∘_; const; flip)

open import Relation.Nullary.Negation.Core using (¬_; contradiction; _¬-⊎_)

private
  variable
    a c : Level
    A B : Set a

------------------------------------------------------------------------
-- `Reflects` idiom.

-- The truth value of A is reflected by a boolean value.
-- `Reflects A b` is equivalent to `if b then A else ¬ A`.

data Reflects (A : Set a) : Bool → Set a where
  ofʸ : ( a :   A) → Reflects A true
  ofⁿ : (¬a : ¬ A) → Reflects A false

------------------------------------------------------------------------
-- Constructors and destructors

-- These lemmas are intended to be used mostly when `b` is a value, so
-- that the conditional expressions have already been evaluated away.

-- NB. not the maximally dependent eliminator, but mostly sufficent

reflects⁻ : (C : Bool → Set c) → (A → C true) → (¬ A → C false) →
            ∀ {b} → Reflects A b → C b
reflects⁻ C t f (ofⁿ ¬a) = f ¬a
reflects⁻ C t f (ofʸ  a) = t a

reflects′ : ∀ (C : Set c) → (A → C) → (¬ A → C) → ∀ {b} → Reflects A b → C
reflects′ C = reflects⁻ (const C)

-- In this case, `of` works like the relevant 'computed constructor'
-- (`ofⁿ` or `ofʸ`), and its inverse `reflects⁻¹` strips off the constructor
-- to just give either the proof of `A` or the proof of `¬ A`.

reflects : ∀ {b} → if b then A else ¬ A → Reflects A b
reflects {b = false} = ofⁿ
reflects {b = true } = ofʸ

reflects⁻¹ : ∀ {b} → Reflects A b → if b then A else ¬ A
reflects⁻¹ {A = A} = reflects⁻ (if_then A else ¬ A) id id

-- in lieu of a distinct `Reflects.Properties` module

reflects⁻¹∘reflects≗id : ∀ {b} (r : if b then A else ¬ A) →
                         reflects⁻¹ (reflects {b = b} r) ≡ r
reflects⁻¹∘reflects≗id {b = false} _ = refl
reflects⁻¹∘reflects≗id {b = true}  _ = refl

reflects∘reflects⁻¹≗id : ∀ {b} (r : Reflects A b) → reflects (reflects⁻¹ r) ≡ r
reflects∘reflects⁻¹≗id (ofʸ a)  = refl
reflects∘reflects⁻¹≗id (ofⁿ ¬a) = refl


------------------------------------------------------------------------
-- Recomputable/recompute

Recomputable : (A : Set a) → Set a
Recomputable A = .A → A

-- Given an irrelevant proof of a reflected type, a proof can
-- be recomputed and subsequently used in relevant contexts.

recompute : ∀ {b} → Reflects A b → Recomputable A
recompute {A = A} = reflects′ (Recomputable A) (λ a _ → a) (λ ¬a a → ⊥-elim (¬a a))

recompute-irr : ∀ {b} (r : Reflects A b) (p q : A) → recompute r p ≡ recompute r q
recompute-irr {A = A} r p q = refl

------------------------------------------------------------------------
-- Interaction with negation, product, sums etc.

infixr 1 _⊎-reflects_
infixr 2 _×-reflects_ _→-reflects_

T-reflects : ∀ b → Reflects (T b) b
T-reflects true  = reflects _
T-reflects false = reflects id

-- If we can decide A, then we can decide its negation.
¬-reflects : ∀ {b} → Reflects A b → Reflects (¬ A) (not b)
¬-reflects {A = A} = reflects⁻ (Reflects (¬ A) ∘ not) (reflects ∘ flip _$_) reflects

-- If we can decide A and B then we can decide their product, sum and implication
_×-reflects_ : ∀ {a b} → Reflects A a → Reflects B b →
               Reflects (A × B) (a ∧ b)
ofʸ  a ×-reflects ofʸ  b = reflects (a , b)
ofʸ  a ×-reflects ofⁿ ¬b = reflects (¬b ∘ proj₂)
ofⁿ ¬a ×-reflects _      = reflects (¬a ∘ proj₁)

_⊎-reflects_ : ∀ {a b} → Reflects A a → Reflects B b →
               Reflects (A ⊎ B) (a ∨ b)
ofʸ  a ⊎-reflects      _ = reflects (inj₁ a)
ofⁿ ¬a ⊎-reflects ofʸ  b = reflects (inj₂ b)
ofⁿ ¬a ⊎-reflects ofⁿ ¬b = reflects (¬a ¬-⊎ ¬b)

_→-reflects_ : ∀ {a b} → Reflects A a → Reflects B b →
               Reflects (A → B) (not a ∨ b)
ofʸ  a →-reflects ofʸ  b = reflects (const b)
ofʸ  a →-reflects ofⁿ ¬b = reflects (¬b ∘ (_$ a))
ofⁿ ¬a →-reflects _      = reflects (flip contradiction ¬a)


------------------------------------------------------------------------
-- Other lemmas

fromEquivalence : ∀ {b} → (T b → A) → (A → T b) → Reflects A b
fromEquivalence {b = true}  sound complete = reflects (sound _)
fromEquivalence {b = false} sound complete = reflects complete

-- `Reflects` is deterministic.
det : ∀ {b b′} → Reflects A b → Reflects A b′ → b ≡ b′
det (ofʸ  a) (ofʸ  _) = refl
det (ofʸ  a) (ofⁿ ¬a) = contradiction a ¬a
det (ofⁿ ¬a) (ofʸ  a) = contradiction a ¬a
det (ofⁿ ¬a) (ofⁿ  _) = refl

T-reflects-elim : ∀ {a b} → Reflects (T a) b → b ≡ a
T-reflects-elim {a} r = det r (T-reflects a)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.1

-- against subsequent deprecation; no warnings issued yet
invert = reflects⁻¹
of = reflects
