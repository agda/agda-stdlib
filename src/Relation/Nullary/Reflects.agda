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
-- that the `if` expressions have already been evaluated away.
-- In this case, `of` works like the relevant constructor (`ofⁿ` or
-- `ofʸ`), and `of⁻¹` strips off the constructor to just give either
-- the proof of `A` or the proof of `¬ A`.

-- NB. not the maximally dependent eliminator, but mostly sufficent

reflects : (C : Bool → Set c) → (A → C true) → (¬ A → C false) →
           ∀ {b} → Reflects A b → C b
reflects C t f (ofⁿ ¬a) = f ¬a
reflects C t f (ofʸ  a) = t a

reflects′ : (A → B) → (¬ A → B) → ∀ {b} → Reflects A b → B
reflects′ {B = B} = reflects (const B)

of : ∀ {b} → if b then A else ¬ A → Reflects A b
of {b = false} ¬a = ofⁿ ¬a
of {b = true }  a = ofʸ a

of⁻¹ : ∀ {b} → Reflects A b → if b then A else ¬ A
of⁻¹ {A = A} = reflects (λ b → if b then A else ¬ A) id id

-- in lieu of a distinct `Reflects.Properties` module

of⁻¹∘of≗id : ∀ {b} (r : if b then A else ¬ A) → of⁻¹ (of {b = b} r) ≡ r
of⁻¹∘of≗id {b = false} _ = refl
of⁻¹∘of≗id {b = true}  _ = refl

of∘of⁻¹≗id : ∀ {b} (r : Reflects A b) → of (of⁻¹ r) ≡ r
of∘of⁻¹≗id (ofʸ a)  = refl
of∘of⁻¹≗id (ofⁿ ¬a) = refl


------------------------------------------------------------------------
-- Recomputable/recompute

Recomputable : (A : Set a) → Set a
Recomputable A = .A → A

-- Given an irrelevant proof of a reflected type, a proof can
-- be recomputed and subsequently used in relevant contexts.

recompute : ∀ {b} → Reflects A b → Recomputable A
recompute {A = A} = reflects′ {B = Recomputable A} (λ a _ → a) (λ ¬a a → ⊥-elim (¬a a))

------------------------------------------------------------------------
-- Interaction with negation, product, sums etc.

infixr 1 _⊎-reflects_
infixr 2 _×-reflects_ _→-reflects_

T-reflects : ∀ b → Reflects (T b) b
T-reflects true  = of _
T-reflects false = of id

-- If we can decide A, then we can decide its negation.
¬-reflects : ∀ {b} → Reflects A b → Reflects (¬ A) (not b)
¬-reflects {A = A} = reflects (λ b → Reflects (¬ A) (not b)) (of ∘ flip _$_) of

-- If we can decide A and Q then we can decide their product
_×-reflects_ : ∀ {a b} → Reflects A a → Reflects B b →
               Reflects (A × B) (a ∧ b)
ofʸ  a ×-reflects ofʸ  b = of (a , b)
ofʸ  a ×-reflects ofⁿ ¬b = of (¬b ∘ proj₂)
ofⁿ ¬a ×-reflects _      = of (¬a ∘ proj₁)

_⊎-reflects_ : ∀ {a b} → Reflects A a → Reflects B b →
               Reflects (A ⊎ B) (a ∨ b)
ofʸ  a ⊎-reflects      _ = of (inj₁ a)
ofⁿ ¬a ⊎-reflects ofʸ  b = of (inj₂ b)
ofⁿ ¬a ⊎-reflects ofⁿ ¬b = of (¬a ¬-⊎ ¬b)

_→-reflects_ : ∀ {a b} → Reflects A a → Reflects B b →
                Reflects (A → B) (not a ∨ b)
ofʸ  a →-reflects ofʸ  b = of (const b)
ofʸ  a →-reflects ofⁿ ¬b = of (¬b ∘ (_$ a))
ofⁿ ¬a →-reflects _      = of (flip contradiction ¬a)


------------------------------------------------------------------------
-- Other lemmas

fromEquivalence : ∀ {b} → (T b → A) → (A → T b) → Reflects A b
fromEquivalence {b = true}  sound complete = of (sound _)
fromEquivalence {b = false} sound complete = of complete

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

invert = of⁻¹ -- against subsequent deprecation; no warning issued yet
