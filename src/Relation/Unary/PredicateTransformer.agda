------------------------------------------------------------------------
-- The Agda standard library
--
-- Predicate transformers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Unary.PredicateTransformer where

open import Data.Product.Base using (∃)
open import Function.Base using (_∘_)
open import Level hiding (_⊔_)
open import Relation.Unary
open import Relation.Binary.Core using (REL)

private
  variable
    a b c i ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Heterogeneous and homogeneous predicate transformers

PT : Set a → Set b → (ℓ₁ ℓ₂ : Level) → Set _
PT A B ℓ₁ ℓ₂ = Pred A ℓ₁ → Pred B ℓ₂

Pt : Set a → (ℓ : Level) → Set _
Pt A ℓ = PT A A ℓ ℓ

------------------------------------------------------------------------
-- Composition and identity

infixr 9 _⍮_

_⍮_ : PT B C ℓ₂ ℓ₃ → PT A B ℓ₁ ℓ₂ → PT A C ℓ₁ _
S ⍮ T = S ∘ T

skip : PT A A ℓ ℓ
skip P = P

------------------------------------------------------------------------
-- Operations on predicates extend pointwise to predicate transformers

-- The bottom and the top of the predicate transformer lattice.

abort : PT A B 0ℓ 0ℓ
abort = λ _ → ∅

magic : PT A B 0ℓ 0ℓ
magic = λ _ → U

-- Negation.

infix 8 ∼_

∼_ : PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂
∼ T = ∁ ∘ T

-- Refinement.

infix 4 _⊑_ _⊒_ _⊑′_ _⊒′_

_⊑_ : PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂ → Set _
S ⊑ T = ∀ {X} → S X ⊆ T X

_⊑′_ : PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂ → Set _
S ⊑′ T = ∀ X → S X ⊆ T X

_⊒_ : PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂ → Set _
T ⊒ S = T ⊑ S

_⊒′_ : PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂ → Set _
T ⊒′ S = S ⊑′ T

-- The dual of refinement.

infix 4 _⋢_

_⋢_ : PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂ → Set _
S ⋢ T = ∃ λ X → S X ≬ T X

-- Union.

infixl 6 _⊓_

_⊓_ : PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂
S ⊓ T = λ X → S X ∪ T X

-- Intersection.

infixl 7 _⊔_

_⊔_ : PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂
S ⊔ T = λ X → S X ∩ T X

-- Implication.

infixl 8 _⇛_

_⇛_ : PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂ → PT A B ℓ₁ ℓ₂
S ⇛ T = λ X → S X ⇒ T X

-- Infinitary union and intersection.

infix 9 ⨆ ⨅

⨆ : ∀ (I : Set i) → (I → PT A B ℓ₁ ℓ₂) → PT A B ℓ₁ _
⨆ I T = λ X → ⋃[ i ∶ I ] T i X

syntax ⨆ I (λ i → T) = ⨆[ i ∶ I ] T

⨅ : ∀ (I : Set i) → (I → PT A B ℓ₁ ℓ₂) → PT A B ℓ₁ _
⨅ I T = λ X → ⋂[ i ∶ I ] T i X

syntax ⨅ I (λ i → T) = ⨅[ i ∶ I ] T

-- Angelic and demonic update.

⟨_⟩ : REL A B ℓ → PT B A ℓ _
⟨ R ⟩ P = λ x → R x ≬ P

[_] : REL A B ℓ → PT B A ℓ _
[ R ] P = λ x → R x ⊆ P
