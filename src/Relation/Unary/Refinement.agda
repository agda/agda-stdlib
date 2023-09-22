------------------------------------------------------------------------
-- The Agda standard library
--
-- Design pattern: refinement types
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Unary.Refinement where

open import Data.Bool.Base using (Bool; T)
open import Level

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

infix 2 RefinementSyntax

RefinementSyntax : (A : Set a) (p : A → Bool) → Set a
RefinementSyntax A p = Refinement p

syntax RefinementSyntax A (λ x → p) = [ x ∈ A || p ]

------------------------------------------------------------------------
-- Export

open Refinement public


