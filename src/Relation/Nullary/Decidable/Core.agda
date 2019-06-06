------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on and properties of decidable relations
--
-- This file contains some core definitions which are re-exported by
-- Relation.Nullary.Decidable
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Decidable.Core where

open import Level using (Level; Lift)
open import Data.Bool.Base using (Bool; false; true; not; T)
open import Data.Unit.Base using (⊤)
open import Data.Empty
open import Data.Product
open import Function

open import Agda.Builtin.Equality
open import Relation.Nullary

private
  variable
    p q : Level
    P : Set p
    Q : Set q

⌊_⌋ : Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false

True : Dec P → Set
True Q = T ⌊ Q ⌋

False : Dec P → Set
False Q = T (not ⌊ Q ⌋)

-- Gives a witness to the "truth".

toWitness : {Q : Dec P} → True Q → P
toWitness {Q = yes p} _  = p
toWitness {Q = no  _} ()

-- Establishes a "truth", given a witness.

fromWitness : {Q : Dec P} → P → True Q
fromWitness {Q = yes p} = const _
fromWitness {Q = no ¬p} = ¬p

-- Variants for False.

toWitnessFalse : {Q : Dec P} → False Q → ¬ P
toWitnessFalse {Q = yes _}  ()
toWitnessFalse {Q = no  ¬p} _  = ¬p

fromWitnessFalse : {Q : Dec P} → ¬ P → False Q
fromWitnessFalse {Q = yes p} = flip _$_ p
fromWitnessFalse {Q = no ¬p} = const _

-- If a decision procedure returns "yes", then we can extract the
-- proof using from-yes.

module _ {p} {P : Set p} where

  From-yes : Dec P → Set p
  From-yes (yes _) = P
  From-yes (no  _) = Lift p ⊤

  from-yes : (p : Dec P) → From-yes p
  from-yes (yes p) = p
  from-yes (no  _) = _

-- If a decision procedure returns "no", then we can extract the proof
-- using from-no.

  From-no : Dec P → Set p
  From-no (no  _) = ¬ P
  From-no (yes _) = Lift p ⊤

  from-no : (p : Dec P) → From-no p
  from-no (no ¬p) = ¬p
  from-no (yes _) = _

------------------------------------------------------------------------
-- Result of decidability

dec-yes : (p? : Dec P) → P → ∃ λ p′ → p? ≡ yes p′
dec-yes (yes p′) p = p′ , refl
dec-yes (no ¬p) p = ⊥-elim (¬p p)

dec-no : (p? : Dec P) → ¬ P → ∃ λ ¬p′ → p? ≡ no ¬p′
dec-no (yes p) ¬p  = ¬p , ⊥-elim (¬p p)
dec-no (no ¬p′) ¬p = ¬p′ , refl

dec-yes-irr : (p? : Dec P) → Irrelevant P → (p : P) → p? ≡ yes p
dec-yes-irr p? irr p with dec-yes p? p
... | p′ , eq rewrite irr p p′ = eq
