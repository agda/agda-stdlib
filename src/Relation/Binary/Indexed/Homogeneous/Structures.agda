------------------------------------------------------------------------
-- The Agda standard library
--
-- Homogeneously-indexed binary relations
------------------------------------------------------------------------

-- The contents of this module should be accessed via
-- `Relation.Binary.Indexed.Homogeneous`.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Indexed.Homogeneous.Core

module Relation.Binary.Indexed.Homogeneous.Structures
  {i a ℓ} {I : Set i}
  (A : I → Set a)   -- The underlying indexed sets
  (_≈ᵢ_ : IRel A ℓ) -- The underlying indexed equality relation
  where

open import Data.Product.Base using (_,_)
open import Function.Base using (_⟨_⟩_)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Core using (_⇒_)
import Relation.Binary.Definitions as B
  using (Reflexive; Symmetric; Transitive; Antisymmetric
        ;_Respectsˡ_; _Respectsʳ_; _Respects₂_)
import Relation.Binary.Structures as B using (IsEquivalence; IsPreorder; IsPartialOrder)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Binary.Indexed.Homogeneous.Definitions
import Relation.Binary.Structures as B
  using (IsEquivalence; IsPreorder; IsPartialOrder)

------------------------------------------------------------------------
-- Equivalences

-- Indexed structures are laid out in a similar manner as to those
-- in Relation.Binary. The main difference is each structure also
-- contains proofs for the lifted version of the relation.

record IsIndexedEquivalence : Set (i ⊔ a ⊔ ℓ) where
  field
    reflᵢ  : Reflexive  A _≈ᵢ_
    symᵢ   : Symmetric  A _≈ᵢ_
    transᵢ : Transitive A _≈ᵢ_

  reflexiveᵢ : ∀ {i} → _≡_ ⟨ _⇒_ ⟩ _≈ᵢ_ {i}
  reflexiveᵢ ≡.refl = reflᵢ

  -- Lift properties

  reflexive : _≡_ ⇒ (Lift A _≈ᵢ_)
  reflexive ≡.refl i = reflᵢ

  refl : B.Reflexive (Lift A _≈ᵢ_)
  refl i = reflᵢ

  sym : B.Symmetric (Lift A _≈ᵢ_)
  sym x≈y i = symᵢ (x≈y i)

  trans : B.Transitive (Lift A _≈ᵢ_)
  trans x≈y y≈z i = transᵢ (x≈y i) (y≈z i)

  isEquivalence : B.IsEquivalence (Lift A _≈ᵢ_)
  isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }


record IsIndexedDecEquivalence : Set (i ⊔ a ⊔ ℓ) where
  infix 4 _≟ᵢ_
  field
    _≟ᵢ_           : Decidable A _≈ᵢ_
    isEquivalenceᵢ : IsIndexedEquivalence

  open IsIndexedEquivalence isEquivalenceᵢ public


------------------------------------------------------------------------
-- Preorders

record IsIndexedPreorder {ℓ₂} (_∼ᵢ_ : IRel A ℓ₂)
                       : Set (i ⊔ a ⊔ ℓ ⊔ ℓ₂) where
  field
    isEquivalenceᵢ : IsIndexedEquivalence
    reflexiveᵢ     : _≈ᵢ_ ⇒[ A ] _∼ᵢ_
    transᵢ         : Transitive A _∼ᵢ_

  module Eq = IsIndexedEquivalence isEquivalenceᵢ

  reflᵢ : Reflexive A _∼ᵢ_
  reflᵢ = reflexiveᵢ Eq.reflᵢ

  ∼ᵢ-respˡ-≈ᵢ : Respectsˡ A _∼ᵢ_ _≈ᵢ_
  ∼ᵢ-respˡ-≈ᵢ x≈y x∼z = transᵢ (reflexiveᵢ (Eq.symᵢ x≈y)) x∼z

  ∼ᵢ-respʳ-≈ᵢ : Respectsʳ A _∼ᵢ_ _≈ᵢ_
  ∼ᵢ-respʳ-≈ᵢ x≈y z∼x = transᵢ z∼x (reflexiveᵢ x≈y)

  ∼ᵢ-resp-≈ᵢ : Respects₂ A _∼ᵢ_ _≈ᵢ_
  ∼ᵢ-resp-≈ᵢ = ∼ᵢ-respʳ-≈ᵢ , ∼ᵢ-respˡ-≈ᵢ

  -- Lifted properties

  reflexive : Lift A _≈ᵢ_ ⇒ Lift A _∼ᵢ_
  reflexive x≈y i = reflexiveᵢ (x≈y i)

  refl : B.Reflexive (Lift A _∼ᵢ_)
  refl i = reflᵢ

  trans : B.Transitive (Lift A _∼ᵢ_)
  trans x≈y y≈z i = transᵢ (x≈y i) (y≈z i)

  ∼-respˡ-≈ : (Lift A _∼ᵢ_) B.Respectsˡ (Lift A _≈ᵢ_)
  ∼-respˡ-≈ x≈y x∼z i = ∼ᵢ-respˡ-≈ᵢ (x≈y i) (x∼z i)

  ∼-respʳ-≈ : (Lift A _∼ᵢ_) B.Respectsʳ (Lift A _≈ᵢ_)
  ∼-respʳ-≈ x≈y z∼x i = ∼ᵢ-respʳ-≈ᵢ (x≈y i) (z∼x i)

  ∼-resp-≈ : (Lift A _∼ᵢ_) B.Respects₂ (Lift A _≈ᵢ_)
  ∼-resp-≈ = ∼-respʳ-≈ , ∼-respˡ-≈

  isPreorder : B.IsPreorder (Lift A _≈ᵢ_) (Lift A _∼ᵢ_)
  isPreorder = record
    { isEquivalence = Eq.isEquivalence
    ; reflexive     = reflexive
    ; trans         = trans
    }


------------------------------------------------------------------------
-- Partial orders

record IsIndexedPartialOrder {ℓ₂} (_≤ᵢ_ : IRel A ℓ₂)
                           : Set (i ⊔ a ⊔ ℓ ⊔ ℓ₂) where
  field
    isPreorderᵢ : IsIndexedPreorder _≤ᵢ_
    antisymᵢ    : Antisymmetric A _≈ᵢ_ _≤ᵢ_

  open IsIndexedPreorder isPreorderᵢ public
    renaming
    ( ∼ᵢ-respˡ-≈ᵢ to ≤ᵢ-respˡ-≈ᵢ
    ; ∼ᵢ-respʳ-≈ᵢ to ≤ᵢ-respʳ-≈ᵢ
    ; ∼ᵢ-resp-≈ᵢ  to ≤ᵢ-resp-≈ᵢ
    ; ∼-respˡ-≈   to ≤-respˡ-≈
    ; ∼-respʳ-≈   to ≤-respʳ-≈
    ; ∼-resp-≈    to ≤-resp-≈
    )

  antisym : B.Antisymmetric (Lift A _≈ᵢ_) (Lift A _≤ᵢ_)
  antisym x≤y y≤x i = antisymᵢ (x≤y i) (y≤x i)

  isPartialOrder : B.IsPartialOrder (Lift A _≈ᵢ_) (Lift A _≤ᵢ_)
  isPartialOrder = record
    { isPreorder = isPreorder
    ; antisym    = antisym
    }
