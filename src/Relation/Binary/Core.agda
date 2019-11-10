------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of binary relations
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Relation.Binary`.

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Core where

open import Function.Base using (_on_)
open import Level using (Level; _⊔_; suc)

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Definitions
------------------------------------------------------------------------

-- Heterogeneous binary relations

REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ suc ℓ)
REL A B ℓ = A → B → Set ℓ

-- Homogeneous binary relations

Rel : Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Rel A ℓ = REL A A ℓ

------------------------------------------------------------------------
-- Relationships between relations
------------------------------------------------------------------------

infixr 4 _⇒_ _=[_]⇒_

-- Implication/containment - could also be written _⊆_.

_⇒_ : REL A B ℓ₁ → REL A B ℓ₂ → Set _
P ⇒ Q = ∀ {x y} → P x y → Q x y

-- Generalised implication - if P ≡ Q it can be read as "f preserves P".

_=[_]⇒_ : Rel A ℓ₁ → (A → B) → Rel B ℓ₂ → Set _
P =[ f ]⇒ Q = P ⇒ (Q on f)

-- A synonym for _=[_]⇒_.

_Preserves_⟶_ : (A → B) → Rel A ℓ₁ → Rel B ℓ₂ → Set _
f Preserves P ⟶ Q = P =[ f ]⇒ Q

-- A binary variant of _Preserves_⟶_.

_Preserves₂_⟶_⟶_ : (A → B → C) → Rel A ℓ₁ → Rel B ℓ₂ → Rel C ℓ₃ → Set _
_∙_ Preserves₂ P ⟶ Q ⟶ R = ∀ {x y u v} → P x y → Q u v → R (x ∙ u) (y ∙ v)
