------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the polymorphic unit type
-- Defines Decidable Equality and Decidable Ordering as well
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Unit.Polymorphic.Properties where

open import Level using (Level)
open import Function.Bundles using (_↔_; mk↔)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁)
open import Data.Unit.Base renaming (⊤ to ⊤*)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Nullary.Decidable using (yes)
open import Relation.Binary.Bundles
  using (Setoid; DecSetoid; Preorder; Poset; TotalOrder; DecTotalOrder)
open import Relation.Binary.Structures
  using (IsPreorder; IsPartialOrder; IsTotalOrder; IsDecTotalOrder)
open import Relation.Binary.Definitions
  using (DecidableEquality; Antisymmetric; Total)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; trans)
open import Relation.Binary.PropositionalEquality.Properties
  using (decSetoid; setoid; isEquivalence)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Equality
------------------------------------------------------------------------

infix 4 _≟_

_≟_ : DecidableEquality (⊤ {ℓ})
_ ≟ _ = yes refl

≡-setoid : ∀ ℓ → Setoid ℓ ℓ
≡-setoid _ = setoid ⊤

≡-decSetoid : ∀ ℓ → DecSetoid ℓ ℓ
≡-decSetoid _ = decSetoid _≟_

------------------------------------------------------------------------
-- Ordering
------------------------------------------------------------------------

≡-total : Total {A = ⊤ {ℓ}} _≡_
≡-total _ _ = inj₁ refl

≡-antisym : Antisymmetric {A = ⊤ {ℓ}} _≡_ _≡_
≡-antisym p _ = p

------------------------------------------------------------------------
-- Structures

≡-isPreorder : ∀ ℓ → IsPreorder {ℓ} {_} {⊤} _≡_ _≡_
≡-isPreorder ℓ = record
  { isEquivalence = isEquivalence
  ; reflexive     = λ x → x
  ; trans         = trans
  }

≡-isPartialOrder : ∀ ℓ → IsPartialOrder {ℓ} _≡_ _≡_
≡-isPartialOrder ℓ = record
  { isPreorder = ≡-isPreorder ℓ
  ; antisym    = ≡-antisym
  }

≡-isTotalOrder : ∀ ℓ → IsTotalOrder {ℓ} _≡_ _≡_
≡-isTotalOrder ℓ = record
  { isPartialOrder = ≡-isPartialOrder ℓ
  ; total          = ≡-total
  }

≡-isDecTotalOrder : ∀ ℓ → IsDecTotalOrder {ℓ} _≡_ _≡_
≡-isDecTotalOrder ℓ = record
  { isTotalOrder = ≡-isTotalOrder ℓ
  ; _≟_          = _≟_
  ; _≤?_         = _≟_
  }

------------------------------------------------------------------------
-- Bundles

≡-preorder : ∀ ℓ → Preorder ℓ ℓ ℓ
≡-preorder ℓ = record
  { isPreorder = ≡-isPreorder ℓ
  }

≡-poset : ∀ ℓ → Poset ℓ ℓ ℓ
≡-poset ℓ = record
  { isPartialOrder = ≡-isPartialOrder ℓ
  }

≡-totalOrder : ∀ ℓ → TotalOrder ℓ ℓ ℓ
≡-totalOrder ℓ = record
  { isTotalOrder = ≡-isTotalOrder ℓ
  }

≡-decTotalOrder : ∀ ℓ → DecTotalOrder ℓ ℓ ℓ
≡-decTotalOrder ℓ = record
  { isDecTotalOrder = ≡-isDecTotalOrder ℓ
  }

⊤↔⊤* : ⊤ {ℓ} ↔ ⊤*
⊤↔⊤* = mk↔ ((λ _ → refl) , (λ _ → refl))
