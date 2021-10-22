------------------------------------------------------------------------
-- The Agda standard library
--
-- The reflexive, symmetric and transitive closure of a binary
-- relation (aka the equivalence closure).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Construct.Closure.Equivalence where

open import Function.Base using (flip; id; _∘_; _on_)
open import Level using (Level; _⊔_)
open import Relation.Binary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (Star; ε; _◅◅_; reverse)
open import Relation.Binary.Construct.Closure.Symmetric as SC
  using (SymClosure)
import Relation.Binary.Construct.On as On

private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A B : Set a
    R S : Rel A ℓ

------------------------------------------------------------------------
-- Definition

EqClosure : {A : Set a} → Rel A ℓ → Rel A (a ⊔ ℓ)
EqClosure R = Star (SymClosure R)

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

------------------------------------------------------------------------
-- Operations

-- A generalised variant of map which allows the index type to change.
gmap : (f : A → B) → R =[ f ]⇒ S → EqClosure R =[ f ]⇒ EqClosure S
gmap f = Star.gmap f ∘ SC.gmap f

map : R ⇒ S → EqClosure R ⇒ EqClosure S
map = gmap id

module _ (S-equiv : IsEquivalence S) (R⇒S : R ⇒ S) where
  open IsEquivalence S-equiv renaming (refl to S-refl; sym to S-sym; trans to S-trans)

  fold : EqClosure R ⇒ S
  fold = Star.fold S (S-trans ∘ SC.fold S-sym R⇒S) S-refl

module _ (S-equiv : IsEquivalence S) (f : A → B) (R⇒S : R =[ f ]⇒ S) where
  gfold : EqClosure R =[ f ]⇒ S
  gfold = fold (On.isEquivalence f S-equiv) R⇒S

return : R ⇒ EqClosure R
return = Star.return ∘ SC.return

join : EqClosure (EqClosure R) ⇒ EqClosure R
join = fold (isEquivalence _) id

infix 10 _⋆

_⋆ : R ⇒ EqClosure S → EqClosure R ⇒ EqClosure S
_⋆ f m = join (map f m)
