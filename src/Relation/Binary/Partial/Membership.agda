------------------------------------------------------------------------
-- The Agda standard library
--
-- Membership in a partial setoid
------------------------------------------------------------------------
{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Partial.Membership {a ℓ} (A : Set a) where

open import Relation.Binary
open import Relation.Binary.Partial

open import Level

------------------------------------------------------------------------
-- Membership

-- An element 'x' of the underlying carrier type of a partial
-- setoid is considered to be a 'member' of a partial
-- setiod when you have a proof of reflexivity

_≈_∈_ : A → A → PartialSetoid A ℓ → Set _
x ≈ y ∈ S = x ≈ y
  where open PartialSetoid S

_≈_∉_ : A → A → PartialSetoid A ℓ → Set _
x ≈ y ∉ S =  x ≉ y
  where open PartialSetoid S

_∈_ : A → PartialSetoid A ℓ → Set _
x ∈ S = x ≈ x ∈ S

_∉_ : A → PartialSetoid A ℓ → Set _
x ∉ S = x ≈ x ∉ S


------------------------------------------------------------------------
-- Restriction

-- We can restrict a partial setoid by imposing extra conditions
-- on the partial equivalence relation

record Restriction {ℓ₁ ℓ₂} (S : PartialSetoid A ℓ₁) (P : A → Set ℓ₂) (x : A) (y : A) : Set (ℓ₁ ⊔ ℓ₂) where
  open PartialSetoid S public
  field
    x≈y : x ≈ y
    P⟨x⟩ : P x
    P⟨y⟩ : P y


restriction-sym : ∀ {ℓ₁ ℓ₂} {S : PartialSetoid A ℓ₁} {P : A → Set ℓ₂} → Symmetric (Restriction S P)
restriction-sym r = record
  { x≈y = sym x≈y
  ; P⟨x⟩ = P⟨y⟩
  ; P⟨y⟩ = P⟨x⟩
  }
  where open Restriction r

restriction-trans : ∀ {ℓ₁ ℓ₂} {S : PartialSetoid A ℓ₁} {P : A → Set ℓ₂} → Transitive (Restriction S P)
restriction-trans r₁ r₂ = record
  { x≈y = trans x≈y y≈z
  ; P⟨x⟩ = P⟨x⟩
  ; P⟨y⟩ = P⟨z⟩
  }
  where open Restriction r₁ using (x≈y; trans; P⟨x⟩)
        open Restriction r₂ using () renaming (x≈y to y≈z; P⟨y⟩ to P⟨z⟩)


⟦_∣_⟧ : ∀ {ℓ₁ ℓ₂} → PartialSetoid A ℓ₁ → (A → Set ℓ₂) → PartialSetoid A (ℓ₁ ⊔ ℓ₂)
⟦ S ∣ P ⟧ = record
  { _≈_ = λ x y → Restriction S P x y
  ; isPartialEquivalence = record
    { sym = restriction-sym
    ; trans = restriction-trans
    }
  }
