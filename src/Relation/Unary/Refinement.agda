------------------------------------------------------------------------
-- The Agda standard library
--
-- Design pattern: refinement types
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Unary.Refinement where

open import Data.Bool.Base using (Bool; T)
open import Function.Base using (_∘_)
open import Level
open import Relation.Nullary.Decidable.Core using (does)
open import Relation.Unary using (Decidable)

private
  variable
    a : Level

------------------------------------------------------------------------
-- Refinement type [ x ∈ A || p ]: like Σ-type, but with irrelevant proj₂

record Refinement {A : Set a} (p : A → Bool) : Set a where

  constructor refine⁺

  field

    refine⁻      : A
    .{{refined}} : T (p refine⁻)

infix 2 RefinementSyntax DecRefinementSyntax

RefinementSyntax : (A : Set a) (p : A → Bool) → Set a
RefinementSyntax A p = Refinement p

syntax RefinementSyntax A (λ x → p) = [ x ∈ A |ᵇ p ]

DecRefinementSyntax : (A : Set a) {P : A → Set} (P? : Decidable P) → Set a
DecRefinementSyntax A P? = Refinement (does ∘ P?)

syntax DecRefinementSyntax A (λ x → P?) = [ x ∈ A |? P? ]

------------------------------------------------------------------------
-- Export: hide irrelevant field name

open Refinement public hiding (refined)

