------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the `Reflects` construct
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Reflects where

open import Agda.Builtin.Equality

open import Data.Bool.Base
open import Data.Empty
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Level using (Level)
open import Function.Base using (_$_; _∘_; const)

open import Relation.Nullary.Negation.Core

private
  variable
    a : Level
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
-- `ofʸ`), and `invert` strips off the constructor to just give either
-- the proof of `A` or the proof of `¬ A`.

of : ∀ {b} → if b then A else ¬ A → Reflects A b
of {b = false} ¬a = ofⁿ ¬a
of {b = true }  a = ofʸ a

invert : ∀ {b} → Reflects A b → if b then A else ¬ A
invert (ofʸ  a) = a
invert (ofⁿ ¬a) = ¬a

------------------------------------------------------------------------
-- Interaction with negation, product, sums etc.

-- If we can decide A, then we can decide its negation.
¬-reflects : ∀ {b} → Reflects A b → Reflects (¬ A) (not b)
¬-reflects (ofʸ  a) = ofⁿ (_$ a)
¬-reflects (ofⁿ ¬a) = ofʸ ¬a

-- If we can decide A and Q then we can decide their product
infixr 2 _×-reflects_
_×-reflects_ : ∀ {a b} → Reflects A a → Reflects B b →
               Reflects (A × B) (a ∧ b)
ofʸ  a ×-reflects ofʸ  b = ofʸ (a , b)
ofʸ  a ×-reflects ofⁿ ¬b = ofⁿ (¬b ∘ proj₂)
ofⁿ ¬a ×-reflects _      = ofⁿ (¬a ∘ proj₁)


infixr 1 _⊎-reflects_
_⊎-reflects_ : ∀ {a b} → Reflects A a → Reflects B b →
               Reflects (A ⊎ B) (a ∨ b)
ofʸ  a ⊎-reflects      _ = ofʸ (inj₁ a)
ofⁿ ¬a ⊎-reflects ofʸ  b = ofʸ (inj₂ b)
ofⁿ ¬a ⊎-reflects ofⁿ ¬b = ofⁿ (¬a ¬-⊎ ¬b)

infixr 2 _→-reflects_
_→-reflects_ : ∀ {a b} → Reflects A a → Reflects B b →
                Reflects (A → B) (not a ∨ b)
ofʸ  a →-reflects ofʸ  b = ofʸ (const b)
ofʸ  a →-reflects ofⁿ ¬b = ofⁿ (¬b ∘ (_$ a))
ofⁿ ¬a →-reflects _      = ofʸ (⊥-elim ∘ ¬a)

------------------------------------------------------------------------
-- Other lemmas

fromEquivalence : ∀ {b} → (T b → A) → (A → T b) → Reflects A b
fromEquivalence {b = true}  sound complete = ofʸ (sound _)
fromEquivalence {b = false} sound complete = ofⁿ complete

-- `Reflects` is deterministic.
det : ∀ {b b′} → Reflects A b → Reflects A b′ → b ≡ b′
det (ofʸ  a) (ofʸ  _) = refl
det (ofʸ  a) (ofⁿ ¬a) = contradiction a ¬a
det (ofⁿ ¬a) (ofʸ  a) = contradiction a ¬a
det (ofⁿ ¬a) (ofⁿ  _) = refl
