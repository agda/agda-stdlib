------------------------------------------------------------------------
-- The Agda standard library
--
-- The reflexive, symmetric and transitive closure of a binary
-- relation (aka the equivalence closure).
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Relation.Binary.Construct.Closure.Equivalence where

open import Function using (flip; id; _∘_)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (Star; ε; _◅◅_; reverse)
open import Relation.Binary.Construct.Closure.Symmetric as SC using (SymClosure)

------------------------------------------------------------------------
-- Definition

EqClosure : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Rel A (a ⊔ ℓ)
EqClosure _∼_ = Star (SymClosure _∼_)

------------------------------------------------------------------------
-- Equivalence closures are equivalences.

module _ {a ℓ} {A : Set a} (_∼_ : Rel A ℓ) where

  reflexive : Reflexive (EqClosure _∼_)
  reflexive = ε

  transitive : Transitive (EqClosure _∼_)
  transitive = _◅◅_

  symmetric : Symmetric (EqClosure _∼_)
  symmetric = reverse (SC.symmetric _∼_)

  isEquivalence : IsEquivalence (EqClosure _∼_)
  isEquivalence = record
    { refl  = reflexive
    ; sym   = symmetric
    ; trans = transitive
    }

  setoid : Setoid a (a ⊔ ℓ)
  setoid = record
    { _≈_           = EqClosure _∼_
    ; isEquivalence = isEquivalence
    }

------------------------------------------------------------------------
-- Operations

module _ {a ℓ₁ ℓ₂ : _} {A : Set a} where

  -- A generalised variant of map which allows the index type to change.

  gmap : ∀ {b} {B : Set b} {P : Rel A ℓ₁} {Q : Rel B ℓ₂} →
         (f : A → B) → P =[ f ]⇒ Q → EqClosure P =[ f ]⇒ EqClosure Q
  gmap {Q = Q} f = Star.gmap f ∘ SC.gmap {Q = Q} f

  map : ∀ {P : Rel A ℓ₁} {Q : Rel A ℓ₂} →
        P ⇒ Q → EqClosure P ⇒ EqClosure Q
  map = gmap id
