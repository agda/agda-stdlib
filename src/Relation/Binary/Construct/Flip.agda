------------------------------------------------------------------------
-- The Agda standard library
--
-- Many properties which hold for `∼` also hold for `flip ∼`. Unlike
-- the module `Relation.Binary.Construct.Converse` this module flips
-- both the relation and the underlying equality.
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Construct.Flip where

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

------------------------------------------------------------------------
-- Structures

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

module _ {a ℓ} where

  setoid : Setoid a ℓ → Setoid a ℓ
  setoid S = record
    { _≈_           = flip S._≈_
    ; isEquivalence = isEquivalence S.isEquivalence
    }
    where module S = Setoid S

  decSetoid : DecSetoid a ℓ → DecSetoid a ℓ
  decSetoid S = record
    { _≈_              = flip S._≈_
    ; isDecEquivalence = isDecEquivalence S.isDecEquivalence
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
