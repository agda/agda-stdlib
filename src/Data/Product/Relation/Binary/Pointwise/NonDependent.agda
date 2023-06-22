------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise products of binary relations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Product.Relation.Binary.Pointwise.NonDependent where

open import Data.Product as Prod
open import Data.Product.Properties using (≡-dec)
open import Data.Sum.Base
open import Data.Unit.Base using (⊤)
open import Function.Base
open import Function.Equality as F using (_⟶_; _⟨$⟩_)
open import Function.Equivalence as Eq
  using (Equivalence; _⇔_; module Equivalence)
open import Function.Injection as Inj
  using (Injection; _↣_; module Injection)
open import Function.Inverse as Inv
  using (Inverse; _↔_; module Inverse)
open import Function.LeftInverse as LeftInv
  using (LeftInverse; _↞_; _LeftInverseOf_; module LeftInverse)
open import Function.Related
open import Function.Surjection as Surj
  using (Surjection; _↠_; module Surjection)
open import Relation.Nullary.Decidable using (_×-dec_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core as P using (_≡_)
import Relation.Binary.PropositionalEquality.Properties as P

module _ {a₁ a₂ ℓ₁ ℓ₂} {A₁ : Set a₁} {A₂ : Set a₂} where

------------------------------------------------------------------------
-- Pointwise lifting

  Pointwise : Rel A₁ ℓ₁ → Rel A₂ ℓ₂ → Rel (A₁ × A₂) _
  Pointwise _∼₁_ _∼₂_ = (_∼₁_ on proj₁) -×- (_∼₂_ on proj₂)

------------------------------------------------------------------------
-- Pointwise preserves many relational properties

  ×-reflexive : ∀ {_≈₁_ _∼₁_ _≈₂_ _∼₂_} →
    _≈₁_ ⇒ _∼₁_ → _≈₂_ ⇒ _∼₂_ →
    (Pointwise _≈₁_ _≈₂_) ⇒ (Pointwise _∼₁_ _∼₂_)
  ×-reflexive refl₁ refl₂ (x∼y₁ , x∼y₂) = refl₁ x∼y₁ , refl₂ x∼y₂

  ×-refl : ∀ {_∼₁_ _∼₂_} →
    Reflexive _∼₁_ → Reflexive _∼₂_ →
    Reflexive (Pointwise _∼₁_ _∼₂_)
  ×-refl refl₁ refl₂ = refl₁ , refl₂

  ×-irreflexive₁ : ∀ {_≈₁_ _<₁_ _≈₂_ _<₂_} →
    Irreflexive _≈₁_ _<₁_ →
    Irreflexive (Pointwise _≈₁_ _≈₂_) (Pointwise _<₁_ _<₂_)
  ×-irreflexive₁ ir x≈y x<y = ir (proj₁ x≈y) (proj₁ x<y)

  ×-irreflexive₂ : ∀ {_≈₁_ _<₁_ _≈₂_ _<₂_} →
    Irreflexive _≈₂_ _<₂_ →
    Irreflexive (Pointwise _≈₁_ _≈₂_) (Pointwise _<₁_ _<₂_)
  ×-irreflexive₂ ir x≈y x<y = ir (proj₂ x≈y) (proj₂ x<y)

  ×-symmetric : ∀ {_∼₁_ _∼₂_} → Symmetric _∼₁_ → Symmetric _∼₂_ →
    Symmetric (Pointwise _∼₁_ _∼₂_)
  ×-symmetric sym₁ sym₂ (x∼y₁ , x∼y₂) = sym₁ x∼y₁ , sym₂ x∼y₂

  ×-transitive : ∀ {_∼₁_ _∼₂_} → Transitive _∼₁_ → Transitive _∼₂_ →
    Transitive (Pointwise _∼₁_ _∼₂_)
  ×-transitive trans₁ trans₂ x∼y y∼z =
    trans₁ (proj₁ x∼y) (proj₁ y∼z) ,
    trans₂ (proj₂ x∼y) (proj₂ y∼z)

  ×-antisymmetric : ∀ {_≈₁_ _≤₁_ _≈₂_ _≤₂_} →
    Antisymmetric _≈₁_ _≤₁_ → Antisymmetric _≈₂_ _≤₂_ →
    Antisymmetric (Pointwise _≈₁_ _≈₂_) (Pointwise _≤₁_ _≤₂_)
  ×-antisymmetric antisym₁ antisym₂ (x≤y₁ , x≤y₂) (y≤x₁ , y≤x₂) =
    (antisym₁ x≤y₁ y≤x₁ , antisym₂ x≤y₂ y≤x₂)

  ×-asymmetric₁ : ∀ {_<₁_ _∼₂_} → Asymmetric _<₁_ →
    Asymmetric (Pointwise _<₁_ _∼₂_)
  ×-asymmetric₁ asym₁ x<y y<x = asym₁ (proj₁ x<y) (proj₁ y<x)

  ×-asymmetric₂ : ∀ {_∼₁_ _<₂_} → Asymmetric _<₂_ →
    Asymmetric (Pointwise _∼₁_ _<₂_)
  ×-asymmetric₂ asym₂ x<y y<x = asym₂ (proj₂ x<y) (proj₂ y<x)

  ×-respects₂ : ∀ {_≈₁_ _∼₁_ _≈₂_ _∼₂_} →
    _∼₁_ Respects₂ _≈₁_ → _∼₂_ Respects₂ _≈₂_ →
    (Pointwise _∼₁_ _∼₂_) Respects₂ (Pointwise _≈₁_ _≈₂_)
  ×-respects₂ {_≈₁_} {_∼₁_} {_≈₂_} {_∼₂_} resp₁ resp₂ = resp¹ , resp²
    where
    _∼_ = Pointwise _∼₁_ _∼₂_
    _≈_ = Pointwise _≈₁_ _≈₂_

    resp¹ : ∀ {x} → (x ∼_) Respects _≈_
    resp¹ y≈y′ x∼y = proj₁ resp₁ (proj₁ y≈y′) (proj₁ x∼y) ,
                     proj₁ resp₂ (proj₂ y≈y′) (proj₂ x∼y)

    resp² : ∀ {y} → (_∼ y) Respects _≈_
    resp² x≈x′ x∼y = proj₂ resp₁ (proj₁ x≈x′) (proj₁ x∼y) ,
                     proj₂ resp₂ (proj₂ x≈x′) (proj₂ x∼y)

  ×-total : ∀ {_∼₁_ _∼₂_} → Symmetric _∼₁_ →
    Total _∼₁_ → Total _∼₂_ →
    Total (Pointwise _∼₁_ _∼₂_)
  ×-total sym₁ total₁ total₂ (x₁ , x₂) (y₁ , y₂)
    with total₁ x₁ y₁ | total₂ x₂ y₂
  ... | inj₁ x₁∼y₁ | inj₁ x₂∼y₂ = inj₁ (     x₁∼y₁ , x₂∼y₂)
  ... | inj₁ x₁∼y₁ | inj₂ y₂∼x₂ = inj₂ (sym₁ x₁∼y₁ , y₂∼x₂)
  ... | inj₂ y₁∼x₁ | inj₂ y₂∼x₂ = inj₂ (     y₁∼x₁ , y₂∼x₂)
  ... | inj₂ y₁∼x₁ | inj₁ x₂∼y₂ = inj₁ (sym₁ y₁∼x₁ , x₂∼y₂)

  ×-decidable : ∀ {_∼₁_ _∼₂_} →
    Decidable _∼₁_ → Decidable _∼₂_ →
    Decidable (Pointwise _∼₁_ _∼₂_)
  ×-decidable _≟₁_ _≟₂_ (x₁ , x₂) (y₁ , y₂) =
    (x₁ ≟₁ y₁) ×-dec (x₂ ≟₂ y₂)

  -- Some collections of properties which are preserved by ×-Rel.

  ×-isEquivalence : ∀ {_≈₁_ _≈₂_} →
    IsEquivalence _≈₁_ → IsEquivalence _≈₂_ →
    IsEquivalence (Pointwise _≈₁_ _≈₂_)
  ×-isEquivalence {_≈₁_ = _≈₁_} {_≈₂_ = _≈₂_} eq₁ eq₂ = record
    { refl  = ×-refl        {_∼₁_ = _≈₁_} {_∼₂_ = _≈₂_}
                            (refl  eq₁) (refl  eq₂)
    ; sym   = ×-symmetric   {_∼₁_ = _≈₁_} {_∼₂_ = _≈₂_}
                            (sym   eq₁) (sym   eq₂)
    ; trans = ×-transitive  {_∼₁_ = _≈₁_} {_∼₂_ = _≈₂_}
                            (trans eq₁) (trans eq₂)
    }
    where open IsEquivalence

  ×-isDecEquivalence : ∀ {_≈₁_ _≈₂_} →
    IsDecEquivalence _≈₁_ → IsDecEquivalence _≈₂_ →
    IsDecEquivalence (Pointwise _≈₁_ _≈₂_)
  ×-isDecEquivalence eq₁ eq₂ = record
    { isEquivalence = ×-isEquivalence
                        (isEquivalence eq₁) (isEquivalence eq₂)
    ; _≟_           = ×-decidable (_≟_ eq₁) (_≟_ eq₂)
    }
    where open IsDecEquivalence

  ×-isPreorder : ∀ {_≈₁_ _∼₁_ _≈₂_ _∼₂_} →
    IsPreorder _≈₁_ _∼₁_ → IsPreorder _≈₂_ _∼₂_ →
    IsPreorder (Pointwise _≈₁_ _≈₂_) (Pointwise _∼₁_ _∼₂_)
  ×-isPreorder {_∼₁_ = _∼₁_} {_∼₂_ = _∼₂_} pre₁ pre₂ = record
    { isEquivalence = ×-isEquivalence
                        (isEquivalence pre₁) (isEquivalence pre₂)
    ; reflexive     = ×-reflexive {_∼₁_ = _∼₁_} {_∼₂_ = _∼₂_}
                        (reflexive pre₁) (reflexive pre₂)
    ; trans         = ×-transitive {_∼₁_ = _∼₁_} {_∼₂_ = _∼₂_}
                        (trans pre₁) (trans pre₂)
    }
    where open IsPreorder

  ×-isPartialOrder : ∀ {_≈₁_ _≤₁_ _≈₂_ _≤₂_} →
    IsPartialOrder _≈₁_ _≤₁_ → IsPartialOrder _≈₂_ _≤₂_ →
    IsPartialOrder (Pointwise _≈₁_ _≈₂_) (Pointwise _≤₁_ _≤₂_)
  ×-isPartialOrder {_≤₁_ = _≤₁_} {_≤₂_ = _≤₂_} po₁ po₂ = record
    { isPreorder = ×-isPreorder (isPreorder po₁) (isPreorder po₂)
    ; antisym    = ×-antisymmetric {_≤₁_ = _≤₁_} {_≤₂_ = _≤₂_}
                     (antisym po₁) (antisym po₂)
    }
    where open IsPartialOrder

  ×-isStrictPartialOrder : ∀ {_≈₁_ _<₁_ _≈₂_ _<₂_} →
    IsStrictPartialOrder _≈₁_ _<₁_ → IsStrictPartialOrder _≈₂_ _<₂_ →
    IsStrictPartialOrder (Pointwise _≈₁_ _≈₂_) (Pointwise _<₁_ _<₂_)
  ×-isStrictPartialOrder {_<₁_ = _<₁_} {_≈₂_ = _≈₂_} {_<₂_ = _<₂_}
                           spo₁ spo₂ =
    record
      { isEquivalence = ×-isEquivalence
                          (isEquivalence spo₁) (isEquivalence spo₂)
      ; irrefl        = ×-irreflexive₁ {_<₁_ = _<₁_} {_≈₂_} {_<₂_}
                          (irrefl spo₁)
      ; trans         = ×-transitive {_∼₁_ = _<₁_} {_<₂_}
                          (trans spo₁) (trans spo₂)
      ; <-resp-≈      = ×-respects₂ (<-resp-≈ spo₁) (<-resp-≈ spo₂)
      }
    where open IsStrictPartialOrder

------------------------------------------------------------------------
-- "Bundles" can also be combined.

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} where

  ×-preorder : Preorder ℓ₁ ℓ₂ _ → Preorder ℓ₃ ℓ₄ _ → Preorder _ _ _
  ×-preorder p₁ p₂ = record
    { isPreorder = ×-isPreorder (isPreorder p₁) (isPreorder p₂)
    } where open Preorder

  ×-setoid : Setoid ℓ₁ ℓ₂ → Setoid ℓ₃ ℓ₄ → Setoid _ _
  ×-setoid s₁ s₂ = record
    { isEquivalence =
        ×-isEquivalence (isEquivalence s₁) (isEquivalence s₂)
    } where open Setoid

  ×-decSetoid : DecSetoid ℓ₁ ℓ₂ → DecSetoid ℓ₃ ℓ₄ → DecSetoid _ _
  ×-decSetoid s₁ s₂ = record
    { isDecEquivalence =
        ×-isDecEquivalence (isDecEquivalence s₁) (isDecEquivalence s₂)
    } where open DecSetoid

  ×-poset : Poset ℓ₁ ℓ₂ _ → Poset ℓ₃ ℓ₄ _ → Poset _ _ _
  ×-poset s₁ s₂ = record
    { isPartialOrder = ×-isPartialOrder (isPartialOrder s₁)
                       (isPartialOrder s₂)
    } where open Poset

  ×-strictPartialOrder :
    StrictPartialOrder ℓ₁ ℓ₂ _ → StrictPartialOrder ℓ₃ ℓ₄ _ →
    StrictPartialOrder _ _ _
  ×-strictPartialOrder s₁ s₂ = record
    { isStrictPartialOrder = ×-isStrictPartialOrder
                               (isStrictPartialOrder s₁)
                               (isStrictPartialOrder s₂)
    } where open StrictPartialOrder

  -- A piece of infix notation for combining setoids
  infix 4 _×ₛ_
  _×ₛ_ : Setoid ℓ₁ ℓ₂ → Setoid ℓ₃ ℓ₄ → Setoid _ _
  _×ₛ_ = ×-setoid

------------------------------------------------------------------------
-- The propositional equality setoid over products can be
-- decomposed using ×-Rel

module _ {a b} {A : Set a} {B : Set b} where

  ≡×≡⇒≡ : Pointwise _≡_ _≡_ ⇒ _≡_ {A = A × B}
  ≡×≡⇒≡ (P.refl , P.refl) = P.refl

  ≡⇒≡×≡ : _≡_ {A = A × B} ⇒ Pointwise _≡_ _≡_
  ≡⇒≡×≡ P.refl = (P.refl , P.refl)

  Pointwise-≡↔≡ : Inverse (P.setoid A ×ₛ P.setoid B) (P.setoid (A × B))
  Pointwise-≡↔≡ = record
    { to         = record { _⟨$⟩_ = id; cong = ≡×≡⇒≡ }
    ; from       = record { _⟨$⟩_ = id; cong = ≡⇒≡×≡ }
    ; inverse-of = record
      { left-inverse-of  = λ _ → (P.refl , P.refl)
      ; right-inverse-of = λ _ → P.refl
      }
    }
