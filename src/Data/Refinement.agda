------------------------------------------------------------------------
-- The Agda standard library
--
-- Refinement type: a value together with a proof irrelevant witness.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Refinement where

open import Level
open import Data.Irrelevant as Irrelevant using (Irrelevant)
open import Function.Base
open import Relation.Unary using (IUniversal; _⇒_; _⊢_)

private
  variable
    a b p q : Level
    A : Set a
    B : Set b

record Refinement {a p} (A : Set a) (P : A → Set p) : Set (a ⊔ p) where
  constructor _,_
  field value : A
        proof : Irrelevant (P value)
open Refinement public

-- The syntax declaration below is meant to mimick set comprehension.
-- It is attached to Refinement-syntax, to make it easy to import
-- Data.Refinement without the special syntax.

infix 2 Refinement-syntax
Refinement-syntax = Refinement
syntax Refinement-syntax A (λ x → P) = [ x ∈ A ∣ P ]

module _ {P : A → Set p} {Q : B → Set q} where

  map : (f : A → B) → ∀[ P ⇒ f ⊢ Q ] →
        [ a ∈ A ∣ P a ] → [ b ∈ B ∣ Q b ]
  map f prf (a , p) = f a , Irrelevant.map prf p

module _ {P : A → Set p} {Q : A → Set q} where

  refine : ∀[ P ⇒ Q ] → [ a ∈ A ∣ P a ] → [ a ∈ A ∣ Q a ]
  refine = map id
