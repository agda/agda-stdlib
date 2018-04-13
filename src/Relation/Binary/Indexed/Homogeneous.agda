------------------------------------------------------------------------
-- The Agda standard library
--
-- Homogeneously-indexed binary relations
------------------------------------------------------------------------

module Relation.Binary.Indexed.Homogeneous where

open import Level using (Level; _⊔_)
import Relation.Binary as B
import Relation.Binary.Indexed as I
open import Relation.Binary.PropositionalEquality as P using (_≡_)

-- Heterogenous, homogenously-indexed relations

REL : ∀ {i a₁ a₂} {I : Set i} → (I → Set a₁) → (I → Set a₂) → (ℓ : Level) → Set _
REL A₁ A₂ ℓ = ∀ {i} → A₁ i → A₂ i → Set ℓ

-- Homogeneous, homogenously-indexed relations

Rel : ∀ {i a} {I : Set i} → (I → Set a) → (ℓ : Level) → Set _
Rel A = REL A A


module _ {i a₁ a₂} {I : Set i} {A₁ : I → Set a₁} {A₂ : I → Set a₂} where

  OverPath
    : ∀ {ℓ} → REL A₁ A₂ ℓ
    → {i j : I} → i ≡ j → B.REL (A₁ i) (A₂ j) ℓ
  OverPath ∼ P.refl = ∼

  toHetIndexed : ∀ {ℓ} → REL A₁ A₂ ℓ → I.REL A₁ A₂ (i ⊔ ℓ)
  toHetIndexed _∼_ {i} {j} x y = (p : i ≡ j) → OverPath _∼_ p x y

  fromHetIndexed : ∀ {ℓ} → I.REL A₁ A₂ ℓ → REL A₁ A₂ ℓ
  fromHetIndexed _∼_ {i} = _∼_ {i} {i}


module _ {i a} {I : Set i} (A : I → Set a) {ℓ} (_∼_ : Rel A ℓ) where
  Reflexive : Set _
  Reflexive = ∀ {i} → B.Reflexive (_∼_ {i})

  Symmetric : Set _
  Symmetric = ∀ {i} → B.Symmetric (_∼_ {i})

  Transitive : Set _
  Transitive = ∀ {i} → B.Transitive (_∼_ {i})

  IsEquivalence : Set _
  IsEquivalence = ∀ {i} → B.IsEquivalence (_∼_ {i})

