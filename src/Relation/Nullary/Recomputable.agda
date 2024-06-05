------------------------------------------------------------------------
-- The Agda standard library
--
-- Recomputable types and their algebra as Harrop formulas
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Recomputable where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Level using (Level)
open import Relation.Nullary.Negation.Core using (¬_)

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definition
--
-- The idea of being 'recomputable' is that, given an *irrelevant* proof
-- of a proposition `A` (signalled by being a value of type `.A`, all of
-- whose inhabitants are identified up to definitional equality, and hence
-- do *not* admit pattern-matching), one may 'promote' such a value to a
-- 'genuine' value of `A`, available for subsequent eg. pattern-matching.

Recomputable : (A : Set a) → Set a
Recomputable A = .A → A

------------------------------------------------------------------------
-- Fundamental property: 'promotion' is a constant function

recompute-constant : (r : Recomputable A) (p q : A) → r p ≡ r q
recompute-constant r p q = refl

------------------------------------------------------------------------
-- Constructions

⊥-recompute : Recomputable ⊥
⊥-recompute ()

_×-recompute_ : Recomputable A → Recomputable B → Recomputable (A × B)
(rA ×-recompute rB) p = rA (p .proj₁) , rB (p .proj₂)

_→-recompute_ : (A : Set a) → Recomputable B → Recomputable (A → B)
(A →-recompute rB) f a = rB (f a)

Π-recompute : (B : A → Set b) → (∀ x → Recomputable (B x)) → Recomputable (∀ x → B x)
Π-recompute B rB f a = rB a (f a)

∀-recompute : (B : A → Set b) → (∀ {x} → Recomputable (B x)) → Recomputable (∀ {x} → B x)
∀-recompute B rB f = rB f

-- corollary: negated propositions are Recomputable

¬-recompute : Recomputable (¬ A)
¬-recompute {A = A} = A →-recompute ⊥-recompute

