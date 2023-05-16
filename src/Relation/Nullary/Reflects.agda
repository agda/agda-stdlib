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
    p q : Level
    P Q : Set p

------------------------------------------------------------------------
-- `Reflects` idiom.

-- The truth value of P is reflected by a boolean value.
-- `Reflects P b` is equivalent to `if b then P else ¬ P`.

data Reflects {p} (P : Set p) : Bool → Set p where
  ofʸ : ( p :   P) → Reflects P true
  ofⁿ : (¬p : ¬ P) → Reflects P false

------------------------------------------------------------------------
-- Constructors and destructors

-- These lemmas are intended to be used mostly when `b` is a value, so
-- that the `if` expressions have already been evaluated away.
-- In this case, `of` works like the relevant constructor (`ofⁿ` or
-- `ofʸ`), and `invert` strips off the constructor to just give either
-- the proof of `P` or the proof of `¬ P`.

of : ∀ {b} → if b then P else ¬ P → Reflects P b
of {b = false} ¬p = ofⁿ ¬p
of {b = true }  p = ofʸ p

invert : ∀ {b} → Reflects P b → if b then P else ¬ P
invert (ofʸ  p) = p
invert (ofⁿ ¬p) = ¬p

------------------------------------------------------------------------
-- Interaction with negation, product, sums etc.

-- If we can decide P, then we can decide its negation.
¬-reflects : ∀ {b} → Reflects P b → Reflects (¬ P) (not b)
¬-reflects (ofʸ  p) = ofⁿ (_$ p)
¬-reflects (ofⁿ ¬p) = ofʸ ¬p

-- If we can decide P and Q then we can decide their product
infixr 2 _×-reflects_
_×-reflects_ : ∀ {a b} → Reflects P a → Reflects Q b →
               Reflects (P × Q) (a ∧ b)
ofʸ  p ×-reflects ofʸ  q = ofʸ (p , q)
ofʸ  p ×-reflects ofⁿ ¬q = ofⁿ (¬q ∘ proj₂)
ofⁿ ¬p ×-reflects _      = ofⁿ (¬p ∘ proj₁)


infixr 1 _⊎-reflects_
_⊎-reflects_ : ∀ {a b} → Reflects P a → Reflects Q b →
               Reflects (P ⊎ Q) (a ∨ b)
ofʸ  p ⊎-reflects      _ = ofʸ (inj₁ p)
ofⁿ ¬p ⊎-reflects ofʸ  q = ofʸ (inj₂ q)
ofⁿ ¬p ⊎-reflects ofⁿ ¬q = ofⁿ (¬p ¬-⊎ ¬q)

infixr 2 _→-reflects_
_→-reflects_ : ∀ {a b} → Reflects P a → Reflects Q b →
                Reflects (P → Q) (not a ∨ b)
ofʸ  p →-reflects ofʸ  q = ofʸ (const q)
ofʸ  p →-reflects ofⁿ ¬q = ofⁿ (¬q ∘ (_$ p))
ofⁿ ¬p →-reflects _      = ofʸ (⊥-elim ∘ ¬p)

------------------------------------------------------------------------
-- Other lemmas

fromEquivalence : ∀ {b} → (T b → P) → (P → T b) → Reflects P b
fromEquivalence {b = true}  sound complete = ofʸ (sound _)
fromEquivalence {b = false} sound complete = ofⁿ complete

-- `Reflects` is deterministic.
det : ∀ {b b′} → Reflects P b → Reflects P b′ → b ≡ b′
det (ofʸ  p) (ofʸ  p′) = refl
det (ofʸ  p) (ofⁿ ¬p′) = ⊥-elim (¬p′ p)
det (ofⁿ ¬p) (ofʸ  p′) = ⊥-elim (¬p p′)
det (ofⁿ ¬p) (ofⁿ ¬p′) = refl
