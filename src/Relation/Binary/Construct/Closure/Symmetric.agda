------------------------------------------------------------------------
-- The Agda standard library
--
-- Symmetric closures of binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Construct.Closure.Symmetric where

open import Function.Base using (id; _on_)
open import Level using (Level; _⊔_)
open import Relation.Binary
import Relation.Binary.Construct.On as On

private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A B : Set a

------------------------------------------------------------------------
-- Definition

data SymClosure {A : Set a} (_∼_ : Rel A ℓ) : Rel A (a ⊔ ℓ) where
  fwd : {a b : A} → a ∼ b → SymClosure _∼_ a b
  bwd : {a b : A} → b ∼ a → SymClosure _∼_ a b

------------------------------------------------------------------------
-- Properties

-- Symmetric closures are symmetric.
symmetric : (_∼_ : Rel A ℓ) → Symmetric (SymClosure _∼_)
symmetric _ (fwd a∼b) = bwd a∼b
symmetric _ (bwd b∼a) = fwd b∼a

------------------------------------------------------------------------
-- Operations

-- A generalised variant of map which allows the index type to change.
gmap : {P : Rel A ℓ₁} {Q : Rel B ℓ₂} (f : A → B) →
       P =[ f ]⇒ Q → SymClosure P =[ f ]⇒ SymClosure Q
gmap _ g (fwd a⟶b) = fwd (g a⟶b)
gmap _ g (bwd a⟵b) = bwd (g a⟵b)

map : {P : Rel A ℓ₁} {Q : Rel A ℓ₂} →
      P ⇒ Q → SymClosure P ⇒ SymClosure Q
map = gmap id

module _ {_⟶_ : Rel A ℓ₁} {_∼_ : Rel A ℓ₂} (∼-symmetric : Symmetric _∼_) (⟶⇒∼ : _⟶_ ⇒ _∼_) where
  lift : SymClosure _⟶_ ⇒ _∼_
  lift (fwd a⟶b) = ⟶⇒∼ a⟶b
  lift (bwd a⟵b) = ∼-symmetric (⟶⇒∼ a⟵b)

  fold : SymClosure _⟶_ ⇒ _∼_
  fold = lift

module _ {_⟶_ : Rel A ℓ₁} {_∼_ : Rel B ℓ₂} (∼-symmetric : Symmetric _∼_) (f : A → B) (⟶⇒∼ : _⟶_ =[ f ]⇒ _∼_) where
  gfold : SymClosure _⟶_ =[ f ]⇒ _∼_
  gfold = fold (On.symmetric f _∼_ ∼-symmetric) ⟶⇒∼

module _ {_⟶_ : Rel A ℓ} where
  return : _⟶_ ⇒ SymClosure _⟶_
  return = fwd

  join : SymClosure (SymClosure _⟶_) ⇒ SymClosure _⟶_
  join = lift (symmetric _⟶_) id

  concat = join

module _ {_⟶₁_ : Rel A ℓ₁} {_⟶₂_ : Rel A ℓ₂} where
  infix 10 _⋆

  _⋆ : _⟶₁_ ⇒ SymClosure _⟶₂_ → SymClosure _⟶₁_ ⇒ SymClosure _⟶₂_
  _⋆ f m = join (map f m)

  infixl 1 _>>=_

  _>>=_ : {a b : A} → SymClosure _⟶₁_ a b → _⟶₁_ ⇒ SymClosure _⟶₂_ → SymClosure _⟶₂_ a b
  m >>= f = (f ⋆) m
