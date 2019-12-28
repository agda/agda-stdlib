------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic definitions for maps to a setoid
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


open import Function using (_∘_)
open import Level using (_⊔_)
open import Relation.Binary using (Rel; _⇒_; Reflexive; Symmetric;
                                   Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module Algebra.Morphism.ToSetoid {α β β=} (A : Set α) (S : Setoid β β=) where

open Setoid S using (_≈_) renaming (Carrier to B; reflexive to ≈reflexive;
                                    refl to ≈refl; sym to ≈sym; trans to ≈trans)
infixl 2 _≈∘_

_≈∘_ :  Rel (A → B) _        -- a generalization for _≗_
f ≈∘ g =  ∀ x → f x ≈ g x

------------------------------------------------------------------------------
-- Properties of _≈∘_

≈∘refl : Reflexive _≈∘_
≈∘refl _ = ≈refl

≈∘reflexive : _≡_ ⇒ _≈∘_
≈∘reflexive {x} refl =  ≈∘refl {x}

≈∘sym : Symmetric _≈∘_
≈∘sym f≈∘g =  ≈sym ∘ f≈∘g

≈∘trans : Transitive _≈∘_
≈∘trans f≈∘g g≈∘h x =  ≈trans (f≈∘g x) (g≈∘h x)

≈∘Equiv : IsEquivalence _≈∘_
≈∘Equiv = record{ refl  = \{x}         → ≈∘refl {x}
                ; sym   = \{x} {y}     → ≈∘sym {x} {y}
                ; trans = \{x} {y} {z} → ≈∘trans {x} {y} {z} }

≈∘Setoid : Setoid (α ⊔ β) (α ⊔ β=)
≈∘Setoid = record{ Carrier       = A → B
                 ; _≈_           = _≈∘_
                 ; isEquivalence = ≈∘Equiv }
