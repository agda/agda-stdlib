------------------------------------------------------------------------
-- The Agda standard library
--
-- Structure of the Action of one (pre-)Setoid on another
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel; _Preserves₂_⟶_⟶_)

module Algebra.Action.Definitions
  {c a ℓ r} {M : Set c} {A : Set a} (_≈ᴹ_ : Rel M ℓ) (_≈_ : Rel A r)
  where

open import Algebra.Core using (Op₂)
open import Function.Base using (id)
open import Level using (Level; _⊔_)

private
  variable
    x y : A
    m n : M



------------------------------------------------------------------------
-- Basic definitions: fix notation

Actˡ : Set (c ⊔ a)
Actˡ = M → A → A

Actʳ : Set (c ⊔ a)
Actʳ = A → M → A

Congruentˡ : Actˡ → Set (c ⊔ a ⊔ ℓ ⊔ r)
Congruentˡ _▷_ = _▷_ Preserves₂ _≈ᴹ_ ⟶ _≈_ ⟶ _≈_

Congruentʳ : Actʳ → Set (c ⊔ a ⊔ ℓ ⊔ r)
Congruentʳ _◁_ = _◁_ Preserves₂ _≈_ ⟶ _≈ᴹ_ ⟶ _≈_

IsActionˡ  : Actˡ → Op₂ M → Set (c ⊔ a ⊔ r)
IsActionˡ _▷_ _∙_ = ∀ m n x → ((m ∙ n) ▷ x) ≈ (m ▷ (n ▷ x))

IsIdentityˡ : Actˡ → M → Set (a ⊔ r)
IsIdentityˡ _▷_ ε = ∀ x → (ε ▷ x) ≈ x

IsActionʳ  : Actʳ → Op₂ M → Set (c ⊔ a ⊔ r)
IsActionʳ _◁_ _∙_ = ∀ x m n → (x ◁ (m ∙ n)) ≈ ((x ◁ m) ◁ n)

IsIdentityʳ : Actʳ → M → Set (a ⊔ r)
IsIdentityʳ _◁_ ε = ∀ x → (x ◁ ε) ≈ x
