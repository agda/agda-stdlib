------------------------------------------------------------------------
-- The Agda standard library
--
-- Homogeneously-indexed binary relations
--
-- Indexed structures are laid out in a similar manner as to those
-- in Relation.Binary. The main difference is each structure also
-- contains proofs for the lifted version of the relation.
------------------------------------------------------------------------

module Relation.Binary.Indexed.Homogeneous where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary as B using (_⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_,_)

------------------------------------------------------------------------
-- Publically export core definitions

open import Relation.Binary.Indexed.Homogeneous.Core public

------------------------------------------------------------------------
-- Equivalences

record IsIndexedEquivalence {i a ℓ} {I : Set i} (A : I → Set a)
                            (_≈ᵢ_ : Rel A ℓ) : Set (i ⊔ a ⊔ ℓ) where
  field
    reflᵢ  : Reflexive  A _≈ᵢ_
    symᵢ   : Symmetric  A _≈ᵢ_
    transᵢ : Transitive A _≈ᵢ_

  -- Lift properties

  reflexive : _≡_ ⇒ (Lift A _≈ᵢ_)
  reflexive P.refl i = reflᵢ

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

record IndexedSetoid {i} (I : Set i) c ℓ : Set (suc (i ⊔ c ⊔ ℓ)) where
  infix 4 _≈ᵢ_ _≈_
  field
    Carrierᵢ       : I → Set c
    _≈ᵢ_           : Rel Carrierᵢ ℓ
    isEquivalenceᵢ : IsIndexedEquivalence Carrierᵢ _≈ᵢ_

  open IsIndexedEquivalence isEquivalenceᵢ public

  Carrier : Set _
  Carrier = ∀ i → Carrierᵢ i

  _≈_ : B.Rel Carrier _
  _≈_ = Lift Carrierᵢ _≈ᵢ_

  _≉_ : B.Rel Carrier _
  x ≉ y = ¬ (x ≈ y)

  setoid : B.Setoid _ _
  setoid = record
    { isEquivalence = isEquivalence
    }

------------------------------------------------------------------------
-- Preorders

record IsIndexedPreorder {i a ℓ₁ ℓ₂} {I : Set i} (A : I → Set a)
                         (_≈ᵢ_ : Rel A ℓ₁) (_∼ᵢ_ : Rel A ℓ₂)
                         : Set (i ⊔ a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isEquivalenceᵢ : IsIndexedEquivalence A _≈ᵢ_
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

  reflexive : Lift A _≈ᵢ_ B.⇒ Lift A _∼ᵢ_
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

record IndexedPreorder {i} (I : Set i) c ℓ₁ ℓ₂ :
                       Set (suc (i ⊔ c ⊔ ℓ₁ ⊔ ℓ₂)) where

  infix 4 _≈ᵢ_ _∼ᵢ_ _≈_ _∼_

  field
    Carrierᵢ    : I → Set c
    _≈ᵢ_        : Rel Carrierᵢ ℓ₁
    _∼ᵢ_        : Rel Carrierᵢ ℓ₂
    isPreorderᵢ : IsIndexedPreorder Carrierᵢ _≈ᵢ_ _∼ᵢ_

  open IsIndexedPreorder isPreorderᵢ public

  Carrier : Set _
  Carrier = ∀ i → Carrierᵢ i

  _≈_ : B.Rel Carrier _
  x ≈ y = ∀ i → x i ≈ᵢ y i

  _∼_ : B.Rel Carrier _
  x ∼ y = ∀ i → x i ∼ᵢ y i

  preorder : B.Preorder _ _ _
  preorder = record { isPreorder = isPreorder }

------------------------------------------------------------------------
-- Partial orders

record IsIndexedPartialOrder {i a ℓ₁ ℓ₂} {I : Set i} (A : I → Set a)
                             (_≈ᵢ_ : Rel A ℓ₁) (_≤ᵢ_ : Rel A ℓ₂) :
                             Set (i ⊔ a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPreorderᵢ : IsIndexedPreorder A _≈ᵢ_ _≤ᵢ_
    antisymᵢ    : Antisymmetric A _≈ᵢ_ _≤ᵢ_

  open IsIndexedPreorder isPreorderᵢ public
    renaming
    ( ∼ᵢ-respˡ-≈ᵢ to ≤ᵢ-respˡ-≈ᵢ
    ; ∼ᵢ-respʳ-≈ᵢ to ≤ᵢ-respʳ-≈ᵢ
    ; ∼ᵢ-resp-≈ᵢ  to ≤ᵢ-resp-≈ᵢ
    ; ∼-respˡ-≈  to ≤-respˡ-≈
    ; ∼-respʳ-≈  to ≤-respʳ-≈
    ; ∼-resp-≈   to ≤-resp-≈
    )

  antisym : B.Antisymmetric (Lift A _≈ᵢ_) (Lift A _≤ᵢ_)
  antisym x≤y y≤x i = antisymᵢ (x≤y i) (y≤x i)

  isPartialOrder : B.IsPartialOrder (Lift A _≈ᵢ_) (Lift A _≤ᵢ_)
  isPartialOrder = record
    { isPreorder = isPreorder
    ; antisym    = antisym
    }

record IndexedPoset {i} (I : Set i) c ℓ₁ ℓ₂ :
                    Set (suc (i ⊔ c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrierᵢ        : I → Set c
    _≈ᵢ_            : Rel Carrierᵢ ℓ₁
    _≤ᵢ_            : Rel Carrierᵢ ℓ₂
    isPartialOrderᵢ : IsIndexedPartialOrder Carrierᵢ _≈ᵢ_ _≤ᵢ_

  open IsIndexedPartialOrder isPartialOrderᵢ public

  preorderᵢ : IndexedPreorder I c ℓ₁ ℓ₂
  preorderᵢ = record { isPreorderᵢ = isPreorderᵢ }

  open IndexedPreorder preorderᵢ public
    using (Carrier; _≈_; preorder)
    renaming
    (_∼_ to _≤_)

  poset : B.Poset _ _ _
  poset = record { isPartialOrder = isPartialOrder }
