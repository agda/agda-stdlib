------------------------------------------------------------------------
-- The Agda standard library
--
-- Orthogonality for types
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Orthogonal where

open import Data.Bool.Base as Bool using (T; true; false; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Empty.Polymorphic renaming (⊥ to ⊥ˡ; ⊥-elim to ⊥ˡ-elim)
open import Data.Product.Base using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; [_,_]′)
open import Data.Unit.Base using (⊤)

open import Function.Base using (const; flip; _∘′_; _$′_)

open import Level using (Level; _⊔_)

open import Relation.Nullary.Negation.Core using (¬_; contradiction)

private
  variable
    a aⁿ b bⁿ p q : Level
    A : Set a
    ¬A : Set aⁿ
    B : Set b
    ¬B : Set bⁿ
    P : Set p
    Q : Set q

------------------------------------------------------------------------
-- Basic definitions

-- Two types are orthogonal with respect to a pole P when assuming
-- that both are inhabited leads to a proof of P.
-- In particular, when the pole is the empty set this amounts to
-- saying that one is a (more or less constructive) notiong of
-- negation for the other.

infix 1 _⫫[_]_
record _⫫[_]_ (A : Set a) (P : Set p) (B : Set b) : Set (p ⊔ a ⊔ b) where
  field orthogonal : A → B → P

  co-orthogonal : B → A → P
  co-orthogonal = flip orthogonal
open _⫫[_]_ public

------------------------------------------------------------------------
-- Base cases

-- The empty type is orthogonal with everything
∅ : ⊥ ⫫[ P ] A
∅ .orthogonal = ⊥-elim

⊘ˡ : ⊥ˡ {a} ⫫[ P ] A
⊘ˡ .orthogonal = ⊥ˡ-elim

-- Truth of a boolean is orthogonal to truth of its negation
Truth : ∀ b → Bool.T b ⫫[ P ] Bool.T (not b)
Truth false .orthogonal = ⊥-elim
Truth true  .orthogonal = flip ⊥-elim

-- A type is always orthogonal to its negation
negation : (A : Set a) → A ⫫[ P ] ¬ A
negation A .orthogonal = contradiction

-- If our notion of orthogonality is with respect to ⊤ then any
-- two things are related
universal : A ⫫[ ⊤ ] B
universal .orthogonal = _

------------------------------------------------------------------------
-- Closure principles

-- The relation is a contravariant bifunctor
map : (B → A) → (P → Q) → (¬B → ¬A) → A ⫫[ P ] ¬A → B ⫫[ Q ] ¬B
map f g ¬f oA .orthogonal b ¬b = g (oA .orthogonal (f b) (¬f ¬b))

-- Being ⊥-orthogonal to the unit type is being uninhabited
uninhabited : ⊤ ⫫[ ⊥ ] A → ¬ A
uninhabited oA = oA .orthogonal _

------------------------------------------------------------------------
-- Type constructors building constructive negations

-- Constructive negation just swaps the two parameters.
-- It is involutive!
∁ : A ⫫[ P ] ¬A → ¬A ⫫[ P ] A
∁ oA .orthogonal a ¬a = oA .orthogonal ¬a a

-- The negation of a function is a proof the domain is inhabited
-- together with a negation of the codomain
_⇒_ : (A : Set a) → B ⫫[ P ] ¬B → (A → B) ⫫[ P ] (A × ¬B)
(oA ⇒ oB) .orthogonal f (a , ¬b) = oB .orthogonal (f a) ¬b

Π : (A : Set a) {B : A → Set b} {¬B : A → Set bⁿ}
  → ((a : A) → B a ⫫[ P ] ¬B a) → ((a : A) → B a) ⫫[ P ] (Σ[ a ∈ A ] ¬B a)
Π A oB .orthogonal f (a , ¬b) = oB a .orthogonal (f a) ¬b

-- The negation of a conjunction is a disjunction of negations
_∩_ : A ⫫[ P ] ¬A → B ⫫[ P ] ¬B → (A × B) ⫫[ P ] (¬A ⊎ ¬B)
(oA ∩ oB) .orthogonal (a , b) =
  [ oA .orthogonal a
  , oB .orthogonal b ]′

Σ : A ⫫[ P ] ¬A → {B : A → Set b} {¬B : A → Set bⁿ} → ((a : A) → B a ⫫[ P ] ¬B a)
  → (Σ[ a ∈ A ] B a) ⫫[ P ] (¬A ⊎ ((a : A) → ¬B a))
Σ oA oB .orthogonal (a , b) =
  [ oA .orthogonal a
  , (λ f → oB a .orthogonal b (f a)) ]′

-- The negation of a strict left-to-right conjunction is defined
-- by either finding a way to disprove A or, a way to disprove B
-- given the knowledge that A is provable
_!∩_ : A ⫫[ P ] ¬A → B ⫫[ P ] ¬B → (A × B) ⫫[ P ] (¬A ⊎ (A × ¬B))
(oA !∩ oB) .orthogonal (a , b) =
  [ oA .orthogonal a
  , oB .orthogonal b ∘′ proj₂ ]′


-- The negation of a disjunction is a conjunction of negations
-- This is defined using de Morgan's law

_∪_ : A ⫫[ P ] ¬A → B ⫫[ P ] ¬B → (A ⊎ B) ⫫[ P ] (¬A × ¬B)
oA ∪ oB = ∁ (∁ oA ∩ ∁ oB)
