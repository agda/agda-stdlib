------------------------------------------------------------------------
-- The Agda standard library
--
-- Homogeneously-indexed binary relations
------------------------------------------------------------------------
-- This file contains some core definitions which are reexported by
-- Relation.Binary.Indexed.Homogeneous

module Relation.Binary.Indexed.Homogeneous.Core where

open import Level using (Level; _⊔_)
open import Data.Product using (_×_)
open import Relation.Binary as B using (REL; Rel)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
import Relation.Binary.Indexed.Heterogeneous as I
open import Relation.Unary.Indexed using (IPred)

------------------------------------------------------------------------
-- Homegeneously indexed binary relations

-- Heterogeneous types

IREL : ∀ {i a b} {I : Set i} → (I → Set a) → (I → Set b) → (ℓ : Level) → Set _
IREL A B ℓ = ∀ {i} → REL (A i) (B i) ℓ

-- Homogeneous types

IRel : ∀ {i a} {I : Set i} → (I → Set a) → (ℓ : Level) → Set _
IRel A = IREL A A

------------------------------------------------------------------------
-- Simple properties

module _ {i a} {I : Set i} (A : I → Set a) where

  syntax Implies A _∼₁_ _∼₂_ = _∼₁_ ⇒[ A ] _∼₂_

  Implies : ∀ {ℓ₁ ℓ₂} → IRel A ℓ₁ → IRel A ℓ₂ → Set _
  Implies _∼₁_ _∼₂_ = ∀ {i} → _∼₁_ B.⇒ (_∼₂_ {i})

  Reflexive : ∀ {ℓ} → IRel A ℓ → Set _
  Reflexive _∼_ = ∀ {i} → B.Reflexive (_∼_ {i})

  Symmetric : ∀ {ℓ} → IRel A ℓ → Set _
  Symmetric _∼_ = ∀ {i} → B.Symmetric (_∼_ {i})

  Transitive : ∀ {ℓ} → IRel A ℓ → Set _
  Transitive _∼_ = ∀ {i} → B.Transitive (_∼_ {i})

  Antisymmetric : ∀ {ℓ₁ ℓ₂} → IRel A ℓ₁ → IRel A ℓ₂ → Set _
  Antisymmetric _≈_ _∼_ = ∀ {i} → B.Antisymmetric _≈_ (_∼_ {i})

  Decidable : ∀ {ℓ} → IRel A ℓ → Set _
  Decidable _∼_ = ∀ {i} → B.Decidable (_∼_ {i})

  Respects : ∀ {ℓ₁ ℓ₂} → IPred A ℓ₁ → IRel A ℓ₂ → Set _
  Respects P _∼_ = ∀ {i} {x y : A i} → x ∼ y → P x → P y

  Respectsˡ : ∀ {ℓ₁ ℓ₂} → IRel A ℓ₁ → IRel A ℓ₂ → Set _
  Respectsˡ P _∼_  = ∀ {i} {x y z : A i} → x ∼ y → P x z → P y z

  Respectsʳ : ∀ {ℓ₁ ℓ₂} → IRel A ℓ₁ → IRel A ℓ₂ → Set _
  Respectsʳ P _∼_ = ∀ {i} {x y z : A i} → x ∼ y → P z x → P z y

  Respects₂ : ∀ {ℓ₁ ℓ₂} → IRel A ℓ₁ → IRel A ℓ₂ → Set _
  Respects₂ P _∼_ = (Respectsʳ P _∼_) × (Respectsˡ P _∼_)

------------------------------------------------------------------------
-- Conversion between homogeneous and heterogeneously indexed relations

module _ {i a b} {I : Set i} {A : I → Set a} {B : I → Set b} where

  OverPath : ∀ {ℓ} → IREL A B ℓ → ∀ {i j} → i ≡ j → REL (A i) (B j) ℓ
  OverPath _∼_ refl = _∼_

  toHetIndexed : ∀ {ℓ} → IREL A B ℓ → I.IREL A B (i ⊔ ℓ)
  toHetIndexed _∼_ {i} {j} x y = (p : i ≡ j) → OverPath _∼_ p x y

  fromHetIndexed : ∀ {ℓ} → I.IREL A B ℓ → IREL A B ℓ
  fromHetIndexed _∼_ = _∼_

------------------------------------------------------------------------
-- Lifting to non-indexed binary relations

module _ {i a} {I : Set i} (A : I → Set a) where

  Lift : ∀ {ℓ} → IRel A ℓ → Rel (∀ i → A i) _
  Lift _∼_ x y = ∀ i → x i ∼ y i
