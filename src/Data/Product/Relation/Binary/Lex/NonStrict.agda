------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic products of binary relations
------------------------------------------------------------------------

-- The definition of lexicographic product used here is suitable if
-- the left-hand relation is a (non-strict) partial order.

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Product.Relation.Binary.Lex.NonStrict where

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as Pointwise
  using (Pointwise)
import Data.Product.Relation.Binary.Lex.Strict as Strict
open import Data.Sum.Base using (inj₁; inj₂)
open import Level using (Level)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles
  using (Poset; DecTotalOrder; TotalOrder)
open import Relation.Binary.Structures
  using (IsPartialOrder; IsEquivalence; IsTotalOrder; IsDecTotalOrder)
open import Relation.Binary.Definitions
  using (Transitive; Symmetric; Decidable; Antisymmetric; Total; Trichotomous
        ; Irreflexive; Asymmetric; _Respects₂_; tri<; tri>; tri≈)
open import Relation.Binary.Consequences
import Relation.Binary.Construct.NonStrictToStrict as Conv


private
  variable
    a b ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definition

×-Lex : (_≈₁_ : Rel A ℓ₁) (_≤₁_ : Rel A ℓ₂) (_≤₂_ : Rel B ℓ₃) →
        Rel (A × B) _
×-Lex _≈₁_ _≤₁_ _≤₂_ = Strict.×-Lex _≈₁_ (Conv._<_ _≈₁_ _≤₁_) _≤₂_

------------------------------------------------------------------------
-- Properties

×-reflexive : (_≈₁_ : Rel A ℓ₁) (_≤₁_ : Rel A ℓ₂)
              {_≈₂_ : Rel B ℓ₃} (_≤₂_ : Rel B ℓ₄) →
              _≈₂_ ⇒ _≤₂_ →
              (Pointwise _≈₁_ _≈₂_) ⇒ (×-Lex _≈₁_ _≤₁_ _≤₂_)
×-reflexive _≈₁_ _≤₁_ _≤₂_ refl₂ =
  Strict.×-reflexive _≈₁_ (Conv._<_ _≈₁_ _≤₁_) _≤₂_ refl₂

module _ {_≈₁_ : Rel A ℓ₁} {_≤₁_ : Rel A ℓ₂} {_≤₂_ : Rel B ℓ₃} where

  private
    _≤ₗₑₓ_ = ×-Lex _≈₁_ _≤₁_ _≤₂_

  ×-transitive : IsPartialOrder _≈₁_ _≤₁_ → Transitive _≤₂_ →
                 Transitive _≤ₗₑₓ_
  ×-transitive po₁ trans₂ =
    Strict.×-transitive {_≈₁_ = _≈₁_} {_<₂_ = _≤₂_}
      isEquivalence (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈)
      (Conv.<-trans _ _ po₁)
      trans₂
    where open IsPartialOrder po₁

  ×-total : Symmetric _≈₁_ → Decidable _≈₁_ → Antisymmetric _≈₁_ _≤₁_ →
            Total _≤₁_ → Total _≤₂_ → Total _≤ₗₑₓ_
  ×-total sym₁ dec₁ antisym₁ total₁ total₂ =
    total
    where
    tri₁ : Trichotomous _≈₁_ (Conv._<_ _≈₁_ _≤₁_)
    tri₁ = Conv.<-trichotomous _ _ sym₁ dec₁ antisym₁ total₁

    total : Total _≤ₗₑₓ_
    total x y with tri₁ (proj₁ x) (proj₁ y)
    ... | tri< x₁<y₁ x₁≉y₁ x₁≯y₁ = inj₁ (inj₁ x₁<y₁)
    ... | tri> x₁≮y₁ x₁≉y₁ x₁>y₁ = inj₂ (inj₁ x₁>y₁)
    ... | tri≈ x₁≮y₁ x₁≈y₁ x₁≯y₁ with total₂ (proj₂ x) (proj₂ y)
    ...   | inj₁ x₂≤y₂ = inj₁ (inj₂ (x₁≈y₁ , x₂≤y₂))
    ...   | inj₂ x₂≥y₂ = inj₂ (inj₂ (sym₁ x₁≈y₁ , x₂≥y₂))

  <ₗₑₓ? : Decidable _≈₁_ → Decidable _≤₁_ → Decidable _≤₂_ →
                Decidable _≤ₗₑₓ_
  <ₗₑₓ? ≈?₁ ≤?₁ ≤?₂ =
    Strict.<ₗₑₓ? ≈?₁ (Conv.<-decidable _ _ ≈?₁ ≤?₁) ≤?₂

module _ {_≈₁_ : Rel A ℓ₁} {_≤₁_ : Rel A ℓ₂}
         {_≈₂_ : Rel B ℓ₃} {_≤₂_ : Rel B ℓ₄}
         where

  private
    _≤ₗₑₓ_ = ×-Lex _≈₁_ _≤₁_ _≤₂_
    _≋_    = Pointwise _≈₁_ _≈₂_

  ×-antisymmetric : IsPartialOrder _≈₁_ _≤₁_ → Antisymmetric _≈₂_ _≤₂_ →
                   Antisymmetric _≋_ _≤ₗₑₓ_
  ×-antisymmetric po₁ antisym₂ =
    Strict.×-antisymmetric {_≈₁_ = _≈₁_} {_<₂_ = _≤₂_}
       ≈-sym₁ irrefl₁ asym₁ antisym₂
    where
    open IsPartialOrder po₁
    open Eq renaming (refl to ≈-refl₁; sym to ≈-sym₁)

    irrefl₁ : Irreflexive _≈₁_ (Conv._<_ _≈₁_ _≤₁_)
    irrefl₁ = Conv.<-irrefl _≈₁_ _≤₁_

    asym₁ : Asymmetric (Conv._<_ _≈₁_ _≤₁_)
    asym₁ = trans∧irr⇒asym {_≈_ = _≈₁_}
                           ≈-refl₁ (Conv.<-trans _ _ po₁) irrefl₁

  ×-respects₂ : IsEquivalence _≈₁_ →
                _≤₁_ Respects₂ _≈₁_ → _≤₂_ Respects₂ _≈₂_ →
                _≤ₗₑₓ_ Respects₂ _≋_
  ×-respects₂ eq₁ resp₁ resp₂ =
    Strict.×-respects₂ eq₁ (Conv.<-resp-≈ _ _ eq₁ resp₁) resp₂


------------------------------------------------------------------------
-- Structures

  ×-isPartialOrder : IsPartialOrder _≈₁_ _≤₁_ →
                     IsPartialOrder _≈₂_ _≤₂_ →
                     IsPartialOrder _≋_ _≤ₗₑₓ_
  ×-isPartialOrder po₁ po₂ = record
    { isPreorder = record
        { isEquivalence = Pointwise.×-isEquivalence
                            (isEquivalence po₁)
                            (isEquivalence po₂)
        ; reflexive     = ×-reflexive _≈₁_ _≤₁_ _≤₂_ (reflexive po₂)
        ; trans         = ×-transitive {_≤₂_ = _≤₂_} po₁ (trans po₂)
        }
    ; antisym = ×-antisymmetric po₁ (antisym po₂)
    }
    where open IsPartialOrder

  ×-isTotalOrder : Decidable _≈₁_ →
                   IsTotalOrder _≈₁_ _≤₁_ →
                   IsTotalOrder _≈₂_ _≤₂_ →
                   IsTotalOrder _≋_ _≤ₗₑₓ_
  ×-isTotalOrder ≈₁-dec to₁ to₂ = record
    { isPartialOrder = ×-isPartialOrder
                         (isPartialOrder to₁) (isPartialOrder to₂)
    ; total          = ×-total (Eq.sym to₁) ≈₁-dec
                                             (antisym to₁) (total to₁)
                               (total to₂)
    }
    where open IsTotalOrder

  ×-isDecTotalOrder : IsDecTotalOrder _≈₁_ _≤₁_ →
                      IsDecTotalOrder _≈₂_ _≤₂_ →
                      IsDecTotalOrder _≋_ _≤ₗₑₓ_
  ×-isDecTotalOrder to₁ to₂ = record
    { isTotalOrder = ×-isTotalOrder (_≟_ to₁)
                                    (isTotalOrder to₁)
                                    (isTotalOrder to₂)
    ; _≟_          = Pointwise.×-decidable (_≟_ to₁) (_≟_ to₂)
    ; _≤?_         = <ₗₑₓ? (_≟_ to₁) (_≤?_ to₁) (_≤?_ to₂)
    }
    where open IsDecTotalOrder

------------------------------------------------------------------------
-- Bundles

×-poset : Poset a ℓ₁ ℓ₂ → Poset b ℓ₃ ℓ₄ → Poset _ _ _
×-poset p₁ p₂ = record
  { isPartialOrder = ×-isPartialOrder O₁.isPartialOrder O₂.isPartialOrder
  } where module O₁ = Poset p₁; module O₂ = Poset p₂

×-totalOrder : DecTotalOrder a ℓ₁ ℓ₂ →
               TotalOrder b ℓ₃ ℓ₄ →
               TotalOrder _ _ _
×-totalOrder t₁ t₂ = record
  { isTotalOrder = ×-isTotalOrder T₁._≟_ T₁.isTotalOrder T₂.isTotalOrder
  } where module T₁ = DecTotalOrder t₁; module T₂ = TotalOrder t₂

×-decTotalOrder : DecTotalOrder a ℓ₁ ℓ₂ →
                  DecTotalOrder b ℓ₃ ℓ₄ →
                  DecTotalOrder _ _ _
×-decTotalOrder t₁ t₂ = record
  { isDecTotalOrder = ×-isDecTotalOrder O₁.isDecTotalOrder O₂.isDecTotalOrder
  } where module O₁ = DecTotalOrder t₁; module O₂ = DecTotalOrder t₂


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.4

×-decidable = <ₗₑₓ?
{-# WARNING_ON_USAGE ×-decidable
"Warning: ×-decidable was deprecated in v2.4.
Please use <ₗₑₓ? instead."
#-}
