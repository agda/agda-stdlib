------------------------------------------------------------------------
-- The Agda standard library
--
-- The reflexive, symmetric and transitive closure of a binary
-- relation (aka the equivalence closure).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Construct.Closure.Equivalence where

open import Function.Base using (flip; id; _∘_)
open import Level using (Level; _⊔_)
open import Relation.Binary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (Star; ε; _◅◅_; reverse)
open import Relation.Binary.Construct.Closure.Symmetric as SC
  using (SymClosure)

private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A B : Set a

------------------------------------------------------------------------
-- Definition

EqClosure : {A : Set a} → Rel A ℓ → Rel A (a ⊔ ℓ)
EqClosure _∼_ = Star (SymClosure _∼_)

------------------------------------------------------------------------
-- Operations

-- A generalised variant of map which allows the index type to change.
gmap : {P : Rel A ℓ₁} {Q : Rel B ℓ₂} →
       (f : A → B) → P =[ f ]⇒ Q → EqClosure P =[ f ]⇒ EqClosure Q
gmap {Q = Q} f = Star.gmap f ∘ SC.gmap {Q = Q} f

map : ∀ {P : Rel A ℓ₁} {Q : Rel A ℓ₂} →
      P ⇒ Q → EqClosure P ⇒ EqClosure Q
map = gmap id

------------------------------------------------------------------------
-- Properties

module _ (_∼_ : Rel A ℓ) where

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

setoid : {A : Set a} (_∼_ : Rel A ℓ) → Setoid a (a ⊔ ℓ)
setoid _∼_ = record
  { _≈_           = EqClosure _∼_
  ; isEquivalence = isEquivalence _∼_
  }
