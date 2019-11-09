------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on nullary relations (like negation and decidability)
------------------------------------------------------------------------

-- Some operations on/properties of nullary relations, i.e. sets.

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary where

open import Agda.Builtin.Equality

open import Data.Bool.Base
open import Data.Empty hiding (⊥-elim)
open import Data.Empty.Irrelevant
open import Level

------------------------------------------------------------------------
-- Negation.

infix 3 ¬_
infix 2 _because_

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⊥

------------------------------------------------------------------------
-- `Reflects` idiom.

-- The truth value of P is reflected by a boolean value.

data Reflects {p} (P : Set p) : Bool → Set p where
  ofʸ : ( p :   P) → Reflects P true
  ofⁿ : (¬p : ¬ P) → Reflects P false

------------------------------------------------------------------------
-- Decidability.

-- This definition allows the boolean portion of the value to compute
-- independently from the proof portion. This translates to better
-- computational properties when we only care about the result and not
-- the proof. See README.Decidability for further details.

record Dec {p} (P : Set p) : Set p where
  constructor _because_
  field
    does : Bool
    proof : Reflects P does

open Dec public

pattern yes p =  true because ofʸ  p
pattern no ¬p = false because ofⁿ ¬p

-- Given an irrelevant proof of a decidable type, a proof can
-- be recomputed and subsequently used in relevant contexts.
recompute : ∀ {a} {A : Set a} → Dec A → .A → A
recompute (yes x) _ = x
recompute (no ¬p) x = ⊥-elim (¬p x)

------------------------------------------------------------------------
-- Irrelevant types

Irrelevant : ∀ {p} → Set p → Set p
Irrelevant P = ∀ (p₁ p₂ : P) → p₁ ≡ p₂
