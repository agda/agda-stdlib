------------------------------------------------------------------------
-- The Agda standard library
--
-- Many properties which hold for `∼` also hold for `flip ∼`. Unlike
-- the module `Relation.Binary.Construct.Flip` this module does not
-- flip the underlying equality.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Construct.Converse where

open import Function
open import Data.Product

------------------------------------------------------------------------
-- Properties

module _ {a ℓ} {A : Set a} (∼ : Rel A ℓ) where

  refl : Reflexive ∼ → Reflexive (flip ∼)
  refl refl = refl

  sym : Symmetric ∼ → Symmetric (flip ∼)
  sym sym = sym

  trans : Transitive ∼ → Transitive (flip ∼)
  trans trans = flip trans

  asym : Asymmetric ∼ → Asymmetric (flip ∼)
  asym asym = asym

  total : Total ∼ → Total (flip ∼)
  total total x y = total y x

  resp : ∀ {p} (P : A → Set p) → Symmetric ∼ →
             P Respects ∼ → P Respects (flip ∼)
  resp _ sym resp ∼ = resp (sym ∼)

  max : ∀ {⊥} → Minimum ∼ ⊥ → Maximum (flip ∼) ⊥
  max min = min

  min : ∀ {⊤} → Maximum ∼ ⊤ → Minimum (flip ∼) ⊤
  min max = max

module _ {a ℓ₁ ℓ₂} {A : Set a} {≈ : Rel A ℓ₁} (∼ : Rel A ℓ₂) where

  reflexive : Symmetric ≈ → (≈ ⇒ ∼) → (≈ ⇒ flip ∼)
  reflexive sym impl = impl ∘ sym

  irrefl : Symmetric ≈ → Irreflexive ≈ ∼ → Irreflexive ≈ (flip ∼)
  irrefl sym irrefl x≈y y∼x = irrefl (sym x≈y) y∼x

  antisym : Antisymmetric ≈ ∼ → Antisymmetric ≈ (flip ∼)
  antisym antisym = flip antisym

  compare : Trichotomous ≈ ∼ → Trichotomous ≈ (flip ∼)
  compare cmp x y with cmp x y
  ... | tri< x<y x≉y y≮x = tri> y≮x x≉y x<y
  ... | tri≈ x≮y x≈y y≮x = tri≈ y≮x x≈y x≮y
  ... | tri> x≮y x≉y y<x = tri< y<x x≉y x≮y

module _ {a ℓ₁ ℓ₂} {A : Set a} (∼₁ : Rel A ℓ₁) (∼₂ : Rel A ℓ₂) where

  resp₂ : ∼₁ Respects₂ ∼₂ → (flip ∼₁) Respects₂ ∼₂
  resp₂ (resp₁ , resp₂) = resp₂ , resp₁

module _ {a b ℓ} {A : Set a} {B : Set b} (∼ : REL A B ℓ) where

  dec : Decidable ∼ → Decidable (flip ∼)
  dec dec = flip dec

------------------------------------------------------------------------
-- Structures

module _ {a ℓ} {A : Set a} {≈ : Rel A ℓ} where

  isPartialEquivalence : IsPartialEquivalence ≈ → IsPartialEquivalence (flip ≈)
  isPartialEquivalence peq = record
    { sym   = sym   ≈ Peq.sym
    ; trans = trans ≈ Peq.trans
    }
    where module Peq = IsPartialEquivalence peq

  isEquivalence : IsEquivalence ≈ → IsEquivalence (flip ≈)
  isEquivalence eq = record
    { refl  = refl  ≈ Eq.refl
    ; isPartialEquivalence = isPartialEquivalence Eq.isPartialEquivalence
    }
    where module Eq = IsEquivalence eq

  isDecEquivalence : IsDecEquivalence ≈ → IsDecEquivalence (flip ≈)
  isDecEquivalence eq = record
    { isEquivalence = isEquivalence Dec.isEquivalence
    ; _≟_           = dec ≈ Dec._≟_
    }
    where module Dec = IsDecEquivalence eq

module _ {a ℓ₁ ℓ₂} {A : Set a} {≈ : Rel A ℓ₁} {∼ : Rel A ℓ₂} where

  isPreorder : IsPreorder ≈ ∼ → IsPreorder ≈ (flip ∼)
  isPreorder O = record
    { isEquivalence = O.isEquivalence
    ; reflexive     = reflexive ∼ O.Eq.sym O.reflexive
    ; trans         = trans ∼ O.trans
    }
    where module O = IsPreorder O

  isPartialOrder : IsPartialOrder ≈ ∼ → IsPartialOrder ≈ (flip ∼)
  isPartialOrder O = record
    { isPreorder = isPreorder O.isPreorder
    ; antisym    = antisym ∼ O.antisym
    }
    where module O = IsPartialOrder O

  isTotalOrder : IsTotalOrder ≈ ∼ → IsTotalOrder ≈ (flip ∼)
  isTotalOrder O = record
    { isPartialOrder = isPartialOrder O.isPartialOrder
    ; total          = total ∼ O.total
    }
    where module O = IsTotalOrder O

  isDecTotalOrder : IsDecTotalOrder ≈ ∼ → IsDecTotalOrder ≈ (flip ∼)
  isDecTotalOrder O = record
    { isTotalOrder = isTotalOrder O.isTotalOrder
    ; _≟_          = O._≟_
    ; _≤?_         = dec ∼ O._≤?_
    }
    where module O = IsDecTotalOrder O

  isStrictPartialOrder : IsStrictPartialOrder ≈ ∼ →
                         IsStrictPartialOrder ≈ (flip ∼)
  isStrictPartialOrder O = record
    { isEquivalence = O.isEquivalence
    ; irrefl        = irrefl ∼ O.Eq.sym O.irrefl
    ; trans         = trans ∼ O.trans
    ; <-resp-≈      = resp₂ ∼ ≈ O.<-resp-≈
    }
    where module O = IsStrictPartialOrder O

  isStrictTotalOrder : IsStrictTotalOrder ≈ ∼ →
                       IsStrictTotalOrder ≈ (flip ∼)
  isStrictTotalOrder O = record
    { isEquivalence = O.isEquivalence
    ; trans         = trans ∼ O.trans
    ; compare       = compare ∼ O.compare
    }
    where module O = IsStrictTotalOrder O

module _ {a ℓ} where

  setoid : Setoid a ℓ → Setoid a ℓ
  setoid S = record
    { isEquivalence = isEquivalence S.isEquivalence
    }
    where module S = Setoid S

  decSetoid : DecSetoid a ℓ → DecSetoid a ℓ
  decSetoid S = record
    { isDecEquivalence = isDecEquivalence S.isDecEquivalence
    }
    where module S = DecSetoid S

module _ {a ℓ₁ ℓ₂} where

  preorder : Preorder a ℓ₁ ℓ₂ → Preorder a ℓ₁ ℓ₂
  preorder O = record
    { isPreorder = isPreorder O.isPreorder
    }
    where module O = Preorder O

  poset : Poset a ℓ₁ ℓ₂ → Poset a ℓ₁ ℓ₂
  poset O = record
    { isPartialOrder = isPartialOrder O.isPartialOrder
    }
    where module O = Poset O

  totalOrder : TotalOrder a ℓ₁ ℓ₂ → TotalOrder a ℓ₁ ℓ₂
  totalOrder O = record
    { isTotalOrder = isTotalOrder O.isTotalOrder
    }
    where module O = TotalOrder O

  decTotalOrder : DecTotalOrder a ℓ₁ ℓ₂ → DecTotalOrder a ℓ₁ ℓ₂
  decTotalOrder O = record
    { isDecTotalOrder = isDecTotalOrder O.isDecTotalOrder
    }
    where module O = DecTotalOrder O

  strictPartialOrder : StrictPartialOrder a ℓ₁ ℓ₂ →
                       StrictPartialOrder a ℓ₁ ℓ₂
  strictPartialOrder O = record
    { isStrictPartialOrder = isStrictPartialOrder O.isStrictPartialOrder
    }
    where module O = StrictPartialOrder O

  strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂ →
                     StrictTotalOrder a ℓ₁ ℓ₂
  strictTotalOrder O = record
    { isStrictTotalOrder = isStrictTotalOrder O.isStrictTotalOrder
    }
    where module O = StrictTotalOrder O
