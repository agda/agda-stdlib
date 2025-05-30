------------------------------------------------------------------------
-- The Agda standard library
--
-- Refinement type: a value together with a proof irrelevant witness.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Refinement.Base where

open import Data.Irrelevant as Irrelevant using (Irrelevant)
open import Function.Base using (id)
open import Level using (Level; _⊔_)
open import Relation.Unary using (IUniversal; _⇒_; _⊢_)

private
  variable
    a b p q : Level
    A : Set a
    B : Set b
    P : A → Set p


------------------------------------------------------------------------
-- Definition

record Refinement (A : Set a) (P : A → Set p) : Set (a ⊔ p) where
  constructor _,_
  field value : A
        proof : Irrelevant (P value)
infixr 4 _,_
open Refinement public

-- The syntax declaration below is meant to mimic set comprehension.
-- It is attached to Refinement-syntax, to make it easy to import
-- Data.Refinement without the special syntax.

infix 2 Refinement-syntax
Refinement-syntax = Refinement
syntax Refinement-syntax A (λ x → P) = [ x ∈ A ∣ P ]

------------------------------------------------------------------------
-- Basic operations

module _ {Q : B → Set q} where

  map : (f : A → B) → ∀[ P ⇒ f ⊢ Q ] →
        [ a ∈ A ∣ P a ] → [ b ∈ B ∣ Q b ]
  map f prf (a , p) = f a , Irrelevant.map prf p

module _ {Q : A → Set q} where

  refine : ∀[ P ⇒ Q ] → [ a ∈ A ∣ P a ] → [ a ∈ A ∣ Q a ]
  refine = map id
