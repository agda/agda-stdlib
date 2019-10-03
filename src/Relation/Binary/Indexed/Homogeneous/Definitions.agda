------------------------------------------------------------------------
-- The Agda standard library
--
-- Homogeneously-indexed binary relations
------------------------------------------------------------------------

-- The contents of this module should be accessed via
-- `Relation.Binary.Indexed.Homogeneous`.

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Indexed.Homogeneous.Definitions where

open import Data.Product using (_×_)
open import Level using (Level)
import Relation.Binary as B
open import Relation.Unary.Indexed using (IPred)

open import Relation.Binary.Indexed.Homogeneous.Core

private
  variable
    i a ℓ ℓ₁ ℓ₂ : Level
    I : Set i

------------------------------------------------------------------------
-- Definitions

module _ (A : I → Set a) where

  syntax Implies A _∼₁_ _∼₂_ = _∼₁_ ⇒[ A ] _∼₂_

  Implies : IRel A ℓ₁ → IRel A ℓ₂ → Set _
  Implies _∼₁_ _∼₂_ = ∀ {i} → _∼₁_ B.⇒ (_∼₂_ {i})

  Reflexive : IRel A ℓ → Set _
  Reflexive _∼_ = ∀ {i} → B.Reflexive (_∼_ {i})

  Symmetric : IRel A ℓ → Set _
  Symmetric _∼_ = ∀ {i} → B.Symmetric (_∼_ {i})

  Transitive : IRel A ℓ → Set _
  Transitive _∼_ = ∀ {i} → B.Transitive (_∼_ {i})

  Antisymmetric : IRel A ℓ₁ → IRel A ℓ₂ → Set _
  Antisymmetric _≈_ _∼_ = ∀ {i} → B.Antisymmetric _≈_ (_∼_ {i})

  Decidable : IRel A ℓ → Set _
  Decidable _∼_ = ∀ {i} → B.Decidable (_∼_ {i})

  Respects : IPred A ℓ₁ → IRel A ℓ₂ → Set _
  Respects P _∼_ = ∀ {i} {x y : A i} → x ∼ y → P x → P y

  Respectsˡ : IRel A ℓ₁ → IRel A ℓ₂ → Set _
  Respectsˡ P _∼_  = ∀ {i} {x y z : A i} → x ∼ y → P x z → P y z

  Respectsʳ : IRel A ℓ₁ → IRel A ℓ₂ → Set _
  Respectsʳ P _∼_ = ∀ {i} {x y z : A i} → x ∼ y → P z x → P z y

  Respects₂ : IRel A ℓ₁ → IRel A ℓ₂ → Set _
  Respects₂ P _∼_ = (Respectsʳ P _∼_) × (Respectsˡ P _∼_)
