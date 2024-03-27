------------------------------------------------------------------------
-- The Agda standard library
--
-- Recomputable types and their algebra as Harrop formulas
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Recomputable where

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Level using (Level)

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definition

Recomputable : (A : Set a) → Set a
Recomputable A = .A → A

------------------------------------------------------------------------
-- Constructions

_×-recompute_ : Recomputable A → Recomputable B → Recomputable (A × B)
(rA ×-recompute rB) p = rA (p .proj₁) , rB (p .proj₂)

_→-recompute_ : (A : Set a) → Recomputable B → Recomputable (A → B)
(A →-recompute rB) f a = rB (f a)

Π-recompute : (B : A → Set b) → (∀ x → Recomputable (B x)) → Recomputable (∀ x → B x)
Π-recompute B rB f a = rB a (f a)

∀-recompute : (B : A → Set b) → (∀ {x} → Recomputable (B x)) → Recomputable (∀ {x} → B x)
∀-recompute B rB f = rB f
