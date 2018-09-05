------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed binary relations
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Relation.Binary.Indexed.

module Relation.Binary.Indexed.Core where

open import Level
import Relation.Binary.Core as B
import Relation.Binary.PropositionalEquality.Core as P

------------------------------------------------------------------------
-- Indexed binary relations

-- Heterogeneous.

REL : ∀ {i₁ i₂ a₁ a₂} {I₁ : Set i₁} {I₂ : Set i₂} →
      (I₁ → Set a₁) → (I₂ → Set a₂) → (ℓ : Level) → Set _
REL A₁ A₂ ℓ = ∀ {i₁ i₂} → A₁ i₁ → A₂ i₂ → Set ℓ

-- Homogeneous.

Rel : ∀ {i a} {I : Set i} → (I → Set a) → (ℓ : Level) → Set _
Rel A ℓ = REL A A ℓ

------------------------------------------------------------------------
-- Simple properties of indexed binary relations

Reflexive : ∀ {i a ℓ} {I : Set i} (A : I → Set a) → Rel A ℓ → Set _
Reflexive _ _∼_ = ∀ {i} → B.Reflexive (_∼_ {i})

Symmetric : ∀ {i a ℓ} {I : Set i} (A : I → Set a) → Rel A ℓ → Set _
Symmetric _ _∼_ = ∀ {i j} → B.Sym (_∼_ {i} {j}) _∼_

Transitive : ∀ {i a ℓ} {I : Set i} (A : I → Set a) → Rel A ℓ → Set _
Transitive _ _∼_ = ∀ {i j k} → B.Trans _∼_ (_∼_ {j}) (_∼_ {i} {k})

-- Generalised implication.

infixr 4 _=[_]⇒_

_=[_]⇒_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : A → Set b} →
          B.Rel A ℓ₁ → ((x : A) → B x) → Rel B ℓ₂ → Set _
P =[ f ]⇒ Q = ∀ {i j} → P i j → Q (f i) (f j)
