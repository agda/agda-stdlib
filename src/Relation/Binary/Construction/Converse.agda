------------------------------------------------------------------------
-- The Agda standard library
--
-- Many properties which hold for `∼` also hold for `flip ∼`. Unlike
-- the module `Relation.Binary.Construction.Flip` this module does not
-- flip the underlying equality.
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Construction.Converse where

open import Function
open import Data.Product

------------------------------------------------------------------------
-- Properties

module _ {a ℓ} {A : Set a} (∼ : Rel A ℓ) where

  reflexive : Reflexive ∼ → Reflexive (flip ∼)
  reflexive refl = refl

  symmetric : Symmetric ∼ → Symmetric (flip ∼)
  symmetric sym = sym

  transitive : Transitive ∼ → Transitive (flip ∼)
  transitive trans = flip trans

  asymmetric : Asymmetric ∼ → Asymmetric (flip ∼)
  asymmetric asym = asym

  total : Total ∼ → Total (flip ∼)
  total total x y = total y x

  respects : ∀ {p} (P : A → Set p) → Symmetric ∼ →
             P Respects ∼ → P Respects flip ∼
  respects _ sym resp ∼ = resp (sym ∼)

  max : ∀ {⊥} → Minimum ∼ ⊥ → Maximum (flip ∼) ⊥
  max min = min

  min : ∀ {⊤} → Maximum ∼ ⊤ → Minimum (flip ∼) ⊤
  min max = max

module _ {a ℓ₁ ℓ₂} {A : Set a} (≈ : Rel A ℓ₁) (∼ : Rel A ℓ₂) where

  implies : Symmetric ≈ → ≈ ⇒ ∼ → ≈ ⇒ flip ∼
  implies sym impl = impl ∘ sym

  irreflexive : Symmetric ≈ → Irreflexive ≈ ∼ → Irreflexive ≈ (flip ∼)
  irreflexive sym irrefl x≈y y∼x = irrefl (sym x≈y) y∼x

  antisymmetric : Antisymmetric ≈ ∼ → Antisymmetric ≈ (flip ∼)
  antisymmetric antisym = flip antisym

  trichotomous : Trichotomous ≈ ∼ → Trichotomous ≈ (flip ∼)
  trichotomous compare x y with compare x y
  ... | tri< x<y x≉y y≮x = tri> y≮x x≉y x<y
  ... | tri≈ x≮y x≈y y≮x = tri≈ y≮x x≈y x≮y
  ... | tri> x≮y x≉y y<x = tri< y<x x≉y x≮y

module _ {a ℓ₁ ℓ₂} {A : Set a} (∼₁ : Rel A ℓ₁) (∼₂ : Rel A ℓ₂) where

  respects₂ : ∼₁ Respects₂ ∼₂ → (flip ∼₁) Respects₂ ∼₂
  respects₂ (resp₁ , resp₂) = resp₂ , resp₁

module _ {a b ℓ} {A : Set a} {B : Set b} (∼ : REL A B ℓ) where

  decidable : Decidable ∼ → Decidable (flip ∼)
  decidable dec x y = dec y x

------------------------------------------------------------------------
-- Structures

module _ {a ℓ} {A : Set a} {≈ : Rel A ℓ} where

  isEquivalence : IsEquivalence ≈ → IsEquivalence (flip ≈)
  isEquivalence eq = record
    { refl  = reflexive  ≈ Eq.refl
    ; sym   = symmetric  ≈ Eq.sym
    ; trans = transitive ≈ Eq.trans
    }
    where module Eq = IsEquivalence eq

  isDecEquivalence : IsDecEquivalence ≈ → IsDecEquivalence (flip ≈)
  isDecEquivalence dec = record
    { isEquivalence = isEquivalence Dec.isEquivalence
    ; _≟_           = decidable ≈ Dec._≟_
    }
    where module Dec = IsDecEquivalence dec

module _ {a ℓ₁ ℓ₂} {A : Set a} {≈ : Rel A ℓ₁} {∼ : Rel A ℓ₂} where

  isPreorder : IsPreorder ≈ ∼ → IsPreorder ≈ (flip ∼)
  isPreorder O = record
    { isEquivalence = O.isEquivalence
    ; reflexive     = implies ≈ ∼ O.Eq.sym O.reflexive
    ; trans         = transitive ∼ O.trans
    }
    where module O = IsPreorder O

  isPartialOrder : IsPartialOrder ≈ ∼ → IsPartialOrder ≈ (flip ∼)
  isPartialOrder O = record
    { isPreorder = isPreorder O.isPreorder
    ; antisym    = antisymmetric ≈ ∼ O.antisym
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
    ; _≤?_         = decidable ∼ O._≤?_
    }
    where module O = IsDecTotalOrder O

  isStrictPartialOrder : IsStrictPartialOrder ≈ ∼ →
                          IsStrictPartialOrder ≈ (flip ∼)
  isStrictPartialOrder O = record
    { isEquivalence = O.isEquivalence
    ; irrefl        = irreflexive ≈ ∼ O.Eq.sym O.irrefl
    ; trans         = transitive ∼ O.trans
    ; <-resp-≈      = respects₂ ∼ ≈ O.<-resp-≈
    }
    where module O = IsStrictPartialOrder O

  isStrictTotalOrder : IsStrictTotalOrder ≈ ∼ →
                        IsStrictTotalOrder ≈ (flip ∼)
  isStrictTotalOrder O = record
    { isEquivalence = O.isEquivalence
    ; trans         = transitive ∼ O.trans
    ; compare       = trichotomous ≈ ∼ O.compare
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
