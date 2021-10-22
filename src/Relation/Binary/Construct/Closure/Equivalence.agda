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

------------------------------------------------------------------------
-- Definition

EqClosure : {A : Set a} → Rel A ℓ → Rel A (a ⊔ ℓ)
EqClosure _∼_ = Star (SymClosure _∼_)

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
gmap : {P : Rel A ℓ₁} {Q : Rel B ℓ₂} →
       (f : A → B) → P =[ f ]⇒ Q → EqClosure P =[ f ]⇒ EqClosure Q
gmap {Q = Q} f = Star.gmap f ∘ SC.gmap {Q = Q} f

map : ∀ {P : Rel A ℓ₁} {Q : Rel A ℓ₂} →
      P ⇒ Q → EqClosure P ⇒ EqClosure Q
map = gmap id

module _ {_⟶_ : Rel A ℓ₁} {_∼_ : Rel A ℓ₂} (∼-equiv : IsEquivalence _∼_) (⟶⇒∼ : _⟶_ ⇒ _∼_) where
  open IsEquivalence ∼-equiv renaming (refl to ∼-refl; sym to ∼-sym; trans to ∼-trans)

  lift : EqClosure _⟶_ ⇒ _∼_
  lift = Star.fold _∼_ (∼-trans ∘ SC.lift ∼-sym ⟶⇒∼) ∼-refl

  fold : EqClosure _⟶_ ⇒ _∼_
  fold = lift

module _ {_⟶_ : Rel A ℓ₁} {_∼_ : Rel B ℓ₂} (∼-equiv : IsEquivalence _∼_) (f : A → B) (⟶⇒∼ : _⟶_ =[ f ]⇒ _∼_) where
  gfold : EqClosure _⟶_ =[ f ]⇒ _∼_
  gfold = fold (On.isEquivalence f ∼-equiv) ⟶⇒∼

module _ {_⟶_ : Rel A ℓ} where
  return : _⟶_ ⇒ EqClosure _⟶_
  return = Star.return ∘ SC.return

  join : EqClosure (EqClosure _⟶_) ⇒ EqClosure _⟶_
  join = lift (isEquivalence _⟶_) id

  concat = join

module _ {_⟶₁_ : Rel A ℓ₁} {_⟶₂_ : Rel A ℓ₂} where
  infix 10 _⋆

  _⋆ : _⟶₁_ ⇒ EqClosure _⟶₂_ → EqClosure _⟶₁_ ⇒ EqClosure _⟶₂_
  _⋆ f m = join (map f m)

  infixl 1 _>>=_

  _>>=_ : {a b : A} → EqClosure _⟶₁_ a b → _⟶₁_ ⇒ EqClosure _⟶₂_ → EqClosure _⟶₂_ a b
  m >>= f = (f ⋆) m
