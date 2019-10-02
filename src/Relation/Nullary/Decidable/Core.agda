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
open import Function.Core

open import Agda.Builtin.Equality
open import Relation.Nullary

private
  variable
    p q : Level
    P : Set p
    p? : Set q

-- `isYes!` is a stricter version of `isYes`, a field of `Dec`.
-- Notice:
--   isYes P? =η= isYes (dec b r) =β= b
--   isYes! P? =η= isYes! (dec b r) ─β↛
-- In these, `r : Respects P b` saves `P`, so we need to keep it to use
-- `toWitness` &c. On the other hand, when we want to do branching,
-- `isYes` will compute more easily.

isYes! : Dec P → Bool
isYes! (dec true  _) = true
isYes! (dec false _) = false

isNo : Dec P → Bool
isNo = not ∘ isYes

isNo! : Dec P → Bool
isNo! = not ∘ isYes!

True : Dec P → Set
True p? = T (isYes p?)

True! : Dec P → Set
True! p? = T (isYes! p?)

False : Dec P → Set
False p? = T (isNo p?)

False! : Dec P → Set
False! p? = T (isNo! p?)

-- Gives a witness to the "truth".

toWitness : (p? : Dec P) → {_ : True p?} → P
toWitness (yes p) = p

toWitness! : {p? : Dec P} → True! p? → P
toWitness! {p? = yes p} _ = p

-- Establishes a "truth", given a witness.

fromWitness : (p? : Dec P) → P → True p?
fromWitness (dec true _) = const _
fromWitness (no      ¬p) = ¬p

fromWitness! : {p? : Dec P} → P → True! p?
fromWitness! {p? = dec true _} = const _
fromWitness! {p? = no      ¬p} = ¬p

-- Variants for False!.

toWitnessFalse : (p? : Dec P) → {_ : False p?} → ¬ P
toWitnessFalse (no ¬p) = ¬p

toWitnessFalse! : {p? : Dec P} → False! p? → ¬ P
toWitnessFalse! {p? = no ¬p} _ = ¬p

fromWitnessFalse : (p? : Dec P) → ¬ P → False p?
fromWitnessFalse (dec false _) = const _
fromWitnessFalse (yes       p) = flip _$_ p

fromWitnessFalse! : {p? : Dec P} → ¬ P → False! p?
fromWitnessFalse! {p? = dec false _} = const _
fromWitnessFalse! {p? = yes       p} = flip _$_ p

-- If a decision procedure returns "yes", then we can extract the
-- proof using from-yes.

module _ {p} {P : Set p} where

  From-yes : Dec P → Set p
  From-yes (dec true  _) = P
  From-yes (dec false _) = Lift p ⊤

  from-yes : (p : Dec P) → From-yes p
  from-yes (yes       p) = p
  from-yes (dec false _) = _

-- If a decision procedure returns "no", then we can extract the proof
-- using from-no.

  From-no : Dec P → Set p
  From-no (dec false _) = ¬ P
  From-no (dec true  _) = Lift p ⊤

  from-no : (p : Dec P) → From-no p
  from-no (no      ¬p) = ¬p
  from-no (dec true _) = _

------------------------------------------------------------------------
-- Result of decidability

dec-yes : (p? : Dec P) → P → ∃ λ p′ → p? ≡ yes p′
dec-yes (no ¬p ) p = ⊥-elim (¬p p)
dec-yes (yes p′) p = p′ , refl

dec-true : (p? : Dec P) → P → isYes p? ≡ true
dec-true (dec true _) _ = refl
dec-true (no      ¬p) p = ⊥-elim (¬p p)

dec-no : (p? : Dec P) → ¬ P → ∃ λ ¬p′ → p? ≡ no ¬p′
dec-no (no ¬p′) ¬p = ¬p′ , refl
dec-no (yes p) ¬p = ⊥-elim (¬p p)

dec-false : (p? : Dec P) → ¬ P → isYes p? ≡ false
dec-false (yes       p) ¬p = ⊥-elim (¬p p)
dec-false (dec false _)  _ = refl

dec-yes-irr : (p? : Dec P) → Irrelevant P → (p : P) → p? ≡ yes p
dec-yes-irr p? irr p with dec-yes p? p
... | p′ , eq rewrite irr p p′ = eq

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.2

⌊_⌋ = isYes!
{-# WARNING_ON_USAGE ⌊_⌋
"Warning: ⌊_⌋ was deprecated in v1.2.
Please use isYes! instead."
#-}
