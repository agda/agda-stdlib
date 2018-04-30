------------------------------------------------------------------------
-- The Agda standard library
--
-- Many properties which hold for `∼` also hold for `flip ∼`
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Flip where

open import Function
open import Data.Product

------------------------------------------------------------------------
-- Properties without equality

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

  min : ∀ {⊥} → Maximum ∼ ⊥ → Minimum (flip ∼) ⊥
  min max = max

module _ {a b ℓ} {A : Set a} {B : Set b} (∼ : REL A B ℓ) where

  decidable : Decidable ∼ → Decidable (flip ∼)
  decidable dec x y = dec y x

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

module _ {a ℓ} where

  setoid : Setoid a ℓ → Setoid a ℓ
  setoid S = record
    { _≈_           = flip S._≈_
    ; isEquivalence = isEquivalence S.isEquivalence
    } where module S = Setoid S

  decSetoid : DecSetoid a ℓ → DecSetoid a ℓ
  decSetoid S = record
    { _≈_              = flip S._≈_
    ; isDecEquivalence = isDecEquivalence S.isDecEquivalence
    } where module S = DecSetoid S

------------------------------------------------------------------------
-- Properties with equality flipped

module _ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
         (≈ : REL A B ℓ₁) (∼ : REL A B ℓ₂) where

  implies : ≈ ⇒ ∼ → flip ≈ ⇒ flip ∼
  implies impl = impl

  irreflexive : Irreflexive ≈ ∼ → Irreflexive (flip ≈) (flip ∼)
  irreflexive irrefl = irrefl

module _ {a ℓ₁ ℓ₂} {A : Set a} (≈ : Rel A ℓ₁) (∼ : Rel A ℓ₂) where

  antisymmetric : Antisymmetric ≈ ∼ → Antisymmetric (flip ≈) (flip ∼)
  antisymmetric antisym = antisym

  trichotomous : Trichotomous ≈ ∼ → Trichotomous (flip ≈) (flip ∼)
  trichotomous compare x y = compare y x

module _ {a ℓ₁ ℓ₂} {A : Set a} (∼₁ : Rel A ℓ₁) (∼₂ : Rel A ℓ₂) where

  respects₂ : Symmetric ∼₂ → ∼₁ Respects₂ ∼₂ → flip ∼₁ Respects₂ flip ∼₂
  respects₂ sym (resp₁ , resp₂) = (resp₂ ∘ sym , resp₁ ∘ sym)

module _ {a ℓ₁ ℓ₂} {A : Set a} {≈ : Rel A ℓ₁} {∼ : Rel A ℓ₂} where

  isPreorder : IsPreorder ≈ ∼ → IsPreorder (flip ≈) (flip ∼)
  isPreorder O = record
    { isEquivalence = isEquivalence O.isEquivalence
    ; reflexive     = implies ≈ ∼ O.reflexive
    ; trans         = transitive ∼ O.trans
    }
    where module O = IsPreorder O

  isPartialOrder : IsPartialOrder ≈ ∼ → IsPartialOrder (flip ≈) (flip ∼)
  isPartialOrder O = record
    { isPreorder = isPreorder O.isPreorder
    ; antisym    = antisymmetric ≈ ∼ O.antisym
    }
    where module O = IsPartialOrder O

  isTotalOrder : IsTotalOrder ≈ ∼ → IsTotalOrder (flip ≈) (flip ∼)
  isTotalOrder O = record
    { isPartialOrder = isPartialOrder O.isPartialOrder
    ; total          = total ∼ O.total
    }
    where module O = IsTotalOrder O

  isDecTotalOrder : IsDecTotalOrder ≈ ∼ → IsDecTotalOrder (flip ≈) (flip ∼)
  isDecTotalOrder O = record
    { isTotalOrder = isTotalOrder O.isTotalOrder
    ; _≟_          = decidable ≈ O._≟_
    ; _≤?_         = decidable ∼ O._≤?_
    }
    where module O = IsDecTotalOrder O

  isStrictPartialOrder : IsStrictPartialOrder ≈ ∼ →
                         IsStrictPartialOrder (flip ≈) (flip ∼)
  isStrictPartialOrder O = record
    { isEquivalence = isEquivalence O.isEquivalence
    ; irrefl        = irreflexive ≈ ∼ O.irrefl
    ; trans         = transitive ∼ O.trans
    ; <-resp-≈      = respects₂ ∼ ≈ O.Eq.sym O.<-resp-≈
    }
    where module O = IsStrictPartialOrder O

  isStrictTotalOrder : IsStrictTotalOrder ≈ ∼ →
                       IsStrictTotalOrder (flip ≈) (flip ∼)
  isStrictTotalOrder O = record
    { isEquivalence = isEquivalence O.isEquivalence
    ; trans         = transitive ∼ O.trans
    ; compare       = trichotomous ≈ ∼ O.compare
    } where module O = IsStrictTotalOrder O

module _ {a ℓ₁ ℓ₂} where

  preorder : Preorder a ℓ₁ ℓ₂ → Preorder a ℓ₁ ℓ₂
  preorder O = record
    { _≈_        = flip O._≈_
    ; _∼_        = flip O._∼_
    ; isPreorder = isPreorder O.isPreorder
    } where module O = Preorder O

  poset : Poset a ℓ₁ ℓ₂ → Poset a ℓ₁ ℓ₂
  poset O = record
    { _≈_            = flip O._≈_
    ; _≤_            = flip O._≤_
    ; isPartialOrder = isPartialOrder O.isPartialOrder
    } where module O = Poset O

  totalOrder : TotalOrder a ℓ₁ ℓ₂ → TotalOrder a ℓ₁ ℓ₂
  totalOrder O = record
    { _≈_          = flip O._≈_
    ; _≤_          = flip O._≤_
    ; isTotalOrder = isTotalOrder O.isTotalOrder
    } where module O = TotalOrder O

  decTotalOrder : DecTotalOrder a ℓ₁ ℓ₂ → DecTotalOrder a ℓ₁ ℓ₂
  decTotalOrder O = record
    { _≈_             = flip O._≈_
    ; _≤_             = flip O._≤_
    ; isDecTotalOrder = isDecTotalOrder O.isDecTotalOrder
    } where module O = DecTotalOrder O

  strictPartialOrder : StrictPartialOrder a ℓ₁ ℓ₂ →
                       StrictPartialOrder a ℓ₁ ℓ₂
  strictPartialOrder O = record
    { _≈_                  = flip O._≈_
    ; _<_                  = flip O._<_
    ; isStrictPartialOrder = isStrictPartialOrder O.isStrictPartialOrder
    } where module O = StrictPartialOrder O

  strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂ →
                     StrictTotalOrder a ℓ₁ ℓ₂
  strictTotalOrder O = record
    { _≈_                = flip O._≈_
    ; _<_                = flip O._<_
    ; isStrictTotalOrder = isStrictTotalOrder O.isStrictTotalOrder
    } where module O = StrictTotalOrder O

------------------------------------------------------------------------
-- Properties with equality unflipped

module _ {a ℓ₁ ℓ₂} {A : Set a} (≈ : Rel A ℓ₁) (∼ : Rel A ℓ₂) where

  impliesᵘ : Symmetric ≈ → ≈ ⇒ ∼ → ≈ ⇒ flip ∼
  impliesᵘ sym impl = impl ∘ sym

  irreflexiveᵘ : Symmetric ≈ → Irreflexive ≈ ∼ → Irreflexive ≈ (flip ∼)
  irreflexiveᵘ sym irrefl x≈y y∼x = irrefl (sym x≈y) y∼x

  antisymmetricᵘ : Antisymmetric ≈ ∼ → Antisymmetric ≈ (flip ∼)
  antisymmetricᵘ antisym = flip antisym

  trichotomousᵘ : Trichotomous ≈ ∼ → Trichotomous ≈ (flip ∼)
  trichotomousᵘ compare x y with compare x y
  ... | tri< x<y x≉y y≮x = tri> y≮x x≉y x<y
  ... | tri≈ x≮y x≈y y≮x = tri≈ y≮x x≈y x≮y
  ... | tri> x≮y x≉y y<x = tri< y<x x≉y x≮y

module _ {a ℓ₁ ℓ₂} {A : Set a} (∼₁ : Rel A ℓ₁) (∼₂ : Rel A ℓ₂) where

  respects₂ᵘ : ∼₁ Respects₂ ∼₂ → (flip ∼₁) Respects₂ ∼₂
  respects₂ᵘ (resp₁ , resp₂) = resp₂ , resp₁

module _ {a ℓ₁ ℓ₂} {A : Set a} {≈ : Rel A ℓ₁} {∼ : Rel A ℓ₂} where

  isPreorderᵘ : IsPreorder ≈ ∼ → IsPreorder ≈ (flip ∼)
  isPreorderᵘ O = record
    { isEquivalence = O.isEquivalence
    ; reflexive     = impliesᵘ ≈ ∼ O.Eq.sym O.reflexive
    ; trans         = transitive ∼ O.trans
    }
    where module O = IsPreorder O

  isPartialOrderᵘ : IsPartialOrder ≈ ∼ → IsPartialOrder ≈ (flip ∼)
  isPartialOrderᵘ O = record
    { isPreorder = isPreorderᵘ O.isPreorder
    ; antisym    = antisymmetricᵘ ≈ ∼ O.antisym
    }
    where module O = IsPartialOrder O

  isTotalOrderᵘ : IsTotalOrder ≈ ∼ → IsTotalOrder ≈ (flip ∼)
  isTotalOrderᵘ O = record
    { isPartialOrder = isPartialOrderᵘ O.isPartialOrder
    ; total          = total ∼ O.total
    }
    where module O = IsTotalOrder O

  isDecTotalOrderᵘ : IsDecTotalOrder ≈ ∼ → IsDecTotalOrder ≈ (flip ∼)
  isDecTotalOrderᵘ O = record
    { isTotalOrder = isTotalOrderᵘ O.isTotalOrder
    ; _≟_          = O._≟_
    ; _≤?_         = decidable ∼ O._≤?_
    }
    where module O = IsDecTotalOrder O

  isStrictPartialOrderᵘ : IsStrictPartialOrder ≈ ∼ →
                          IsStrictPartialOrder ≈ (flip ∼)
  isStrictPartialOrderᵘ O = record
    { isEquivalence = O.isEquivalence
    ; irrefl        = irreflexiveᵘ ≈ ∼ O.Eq.sym O.irrefl
    ; trans         = transitive ∼ O.trans
    ; <-resp-≈      = respects₂ᵘ ∼ ≈ O.<-resp-≈
    }
    where module O = IsStrictPartialOrder O

  isStrictTotalOrderᵘ : IsStrictTotalOrder ≈ ∼ →
                        IsStrictTotalOrder ≈ (flip ∼)
  isStrictTotalOrderᵘ O = record
    { isEquivalence = O.isEquivalence
    ; trans         = transitive ∼ O.trans
    ; compare       = trichotomousᵘ ≈ ∼ O.compare
    } where module O = IsStrictTotalOrder O

module _ {a ℓ₁ ℓ₂} where

  preorderᵘ : Preorder a ℓ₁ ℓ₂ → Preorder a ℓ₁ ℓ₂
  preorderᵘ O = record
    { _≈_        = O._≈_
    ; _∼_        = flip O._∼_
    ; isPreorder = isPreorderᵘ O.isPreorder
    } where module O = Preorder O

  posetᵘ : Poset a ℓ₁ ℓ₂ → Poset a ℓ₁ ℓ₂
  posetᵘ O = record
    { _≈_            = O._≈_
    ; _≤_            = flip O._≤_
    ; isPartialOrder = isPartialOrderᵘ O.isPartialOrder
    } where module O = Poset O

  totalOrderᵘ : TotalOrder a ℓ₁ ℓ₂ → TotalOrder a ℓ₁ ℓ₂
  totalOrderᵘ O = record
    { _≈_          = O._≈_
    ; _≤_          = flip O._≤_
    ; isTotalOrder = isTotalOrderᵘ O.isTotalOrder
    } where module O = TotalOrder O

  decTotalOrderᵘ : DecTotalOrder a ℓ₁ ℓ₂ → DecTotalOrder a ℓ₁ ℓ₂
  decTotalOrderᵘ O = record
    { _≈_             = O._≈_
    ; _≤_             = flip O._≤_
    ; isDecTotalOrder = isDecTotalOrderᵘ O.isDecTotalOrder
    } where module O = DecTotalOrder O

  strictPartialOrderᵘ : StrictPartialOrder a ℓ₁ ℓ₂ →
                        StrictPartialOrder a ℓ₁ ℓ₂
  strictPartialOrderᵘ O = record
    { _≈_                  = O._≈_
    ; _<_                  = flip O._<_
    ; isStrictPartialOrder = isStrictPartialOrderᵘ O.isStrictPartialOrder
    } where module O = StrictPartialOrder O

  strictTotalOrderᵘ : StrictTotalOrder a ℓ₁ ℓ₂ →
                      StrictTotalOrder a ℓ₁ ℓ₂
  strictTotalOrderᵘ O = record
    { _≈_                = O._≈_
    ; _<_                = flip O._<_
    ; isStrictTotalOrder = isStrictTotalOrderᵘ O.isStrictTotalOrder
    } where module O = StrictTotalOrder O
