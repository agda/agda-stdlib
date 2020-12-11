------------------------------------------------------------------------
-- The Agda standard library
--
-- Many properties which hold for `_∼_` also hold for `_∼_ on f`
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Construct.On where

open import Data.Product
open import Function.Base using (_on_; _∘_)
open import Induction.WellFounded using (WellFounded; Acc; acc)
open import Level using (Level)
open import Relation.Binary

private
  variable
    a b p ℓ ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definitions

module _ (f : B → A) where

  implies : (≈ : Rel A ℓ₁) (∼ : Rel A ℓ₂) →
            ≈ ⇒ ∼ → (≈ on f) ⇒ (∼ on f)
  implies _ _ impl = impl

  reflexive : (∼ : Rel A ℓ) → Reflexive ∼ → Reflexive (∼ on f)
  reflexive _ refl = refl

  irreflexive : (≈ : Rel A ℓ₁) (∼ : Rel A ℓ₂) →
                Irreflexive ≈ ∼ → Irreflexive (≈ on f) (∼ on f)
  irreflexive _ _ irrefl = irrefl

  symmetric : (∼ : Rel A ℓ) → Symmetric ∼ → Symmetric (∼ on f)
  symmetric _ sym = sym

  transitive : (∼ : Rel A ℓ) → Transitive ∼ → Transitive (∼ on f)
  transitive _ trans = trans

  antisymmetric : (≈ : Rel A ℓ₁) (≤ : Rel A ℓ₂) →
                  Antisymmetric ≈ ≤ → Antisymmetric (≈ on f) (≤ on f)
  antisymmetric _ _ antisym = antisym

  asymmetric : (< : Rel A ℓ) → Asymmetric < → Asymmetric (< on f)
  asymmetric _ asym = asym

  respects : (∼ : Rel A ℓ) (P : A → Set p) →
             P Respects ∼ → (P ∘ f) Respects (∼ on f)
  respects _ _ resp = resp

  respects₂ : (∼₁ : Rel A ℓ₁) (∼₂ : Rel A ℓ₂) →
              ∼₁ Respects₂ ∼₂ → (∼₁ on f) Respects₂ (∼₂ on f)
  respects₂ _ _ (resp₁ , resp₂) = (resp₁ , resp₂)

  decidable : (∼ : Rel A ℓ) → Decidable ∼ → Decidable (∼ on f)
  decidable _ dec x y = dec (f x) (f y)

  total : (∼ : Rel A ℓ) → Total ∼ → Total (∼ on f)
  total _ tot x y = tot (f x) (f y)

  trichotomous : (≈ : Rel A ℓ₁) (< : Rel A ℓ₂) →
                 Trichotomous ≈ < → Trichotomous (≈ on f) (< on f)
  trichotomous _ _ compare x y = compare (f x) (f y)

  accessible : ∀ {∼ : Rel A ℓ} {x} → Acc ∼ (f x) → Acc (∼ on f) x
  accessible (acc rs) = acc (λ y fy<fx → accessible (rs (f y) fy<fx))

  wellFounded : {∼ : Rel A ℓ} → WellFounded ∼ → WellFounded (∼ on f)
  wellFounded wf x = accessible (wf (f x))

------------------------------------------------------------------------
-- Structures

module _ (f : B → A) {≈ : Rel A ℓ₁} where

  isEquivalence : IsEquivalence ≈ →
                  IsEquivalence (≈ on f)
  isEquivalence eq = record
    { refl  = reflexive  f ≈ Eq.refl
    ; sym   = symmetric  f ≈ Eq.sym
    ; trans = transitive f ≈ Eq.trans
    } where module Eq = IsEquivalence eq

  isDecEquivalence : IsDecEquivalence ≈ →
                     IsDecEquivalence (≈ on f)
  isDecEquivalence dec = record
    { isEquivalence = isEquivalence Dec.isEquivalence
    ; _≟_           = decidable f ≈ Dec._≟_
    } where module Dec = IsDecEquivalence dec

module _ (f : B → A) {≈ : Rel A ℓ₁} {∼ : Rel A ℓ₂} where

  isPreorder : IsPreorder ≈ ∼ → IsPreorder (≈ on f) (∼ on f)
  isPreorder pre = record
    { isEquivalence = isEquivalence f Pre.isEquivalence
    ; reflexive     = implies f ≈ ∼ Pre.reflexive
    ; trans         = transitive f ∼ Pre.trans
    } where module Pre = IsPreorder pre

  isPartialOrder : IsPartialOrder ≈ ∼ →
                   IsPartialOrder (≈ on f) (∼ on f)
  isPartialOrder po = record
    { isPreorder = isPreorder Po.isPreorder
    ; antisym    = antisymmetric f ≈ ∼ Po.antisym
    } where module Po = IsPartialOrder po

  isDecPartialOrder : IsDecPartialOrder ≈ ∼ →
                      IsDecPartialOrder (≈ on f) (∼ on f)
  isDecPartialOrder dpo = record
    { isPartialOrder = isPartialOrder DPO.isPartialOrder
    ; _≟_            = decidable f _ DPO._≟_
    ; _≤?_           = decidable f _ DPO._≤?_
    } where module DPO = IsDecPartialOrder dpo

  isStrictPartialOrder : IsStrictPartialOrder ≈ ∼ →
                         IsStrictPartialOrder (≈ on f) (∼ on f)
  isStrictPartialOrder spo = record
    { isEquivalence = isEquivalence f Spo.isEquivalence
    ; irrefl        = irreflexive f ≈ ∼ Spo.irrefl
    ; trans         = transitive f ∼ Spo.trans
    ; <-resp-≈      = respects₂ f ∼ ≈ Spo.<-resp-≈
    } where module Spo = IsStrictPartialOrder spo

  isTotalOrder : IsTotalOrder ≈ ∼ →
                 IsTotalOrder (≈ on f) (∼ on f)
  isTotalOrder to = record
    { isPartialOrder = isPartialOrder To.isPartialOrder
    ; total          = total f ∼ To.total
    } where module To = IsTotalOrder to

  isDecTotalOrder : IsDecTotalOrder ≈ ∼ →
                    IsDecTotalOrder (≈ on f) (∼ on f)
  isDecTotalOrder dec = record
    { isTotalOrder = isTotalOrder Dec.isTotalOrder
    ; _≟_          = decidable f ≈ Dec._≟_
    ; _≤?_         = decidable f ∼ Dec._≤?_
    } where module Dec = IsDecTotalOrder dec

  isStrictTotalOrder : IsStrictTotalOrder ≈ ∼ →
                       IsStrictTotalOrder (≈ on f) (∼ on f)
  isStrictTotalOrder sto = record
    { isEquivalence = isEquivalence f Sto.isEquivalence
    ; trans         = transitive f ∼ Sto.trans
    ; compare       = trichotomous f ≈ ∼ Sto.compare
    } where module Sto = IsStrictTotalOrder sto

------------------------------------------------------------------------
-- Bundles

preorder : (P : Preorder a ℓ₁ ℓ₂) →
           (B → Preorder.Carrier P) →
           Preorder _ _ _
preorder P f = record
  { isPreorder = isPreorder f (Preorder.isPreorder P)
  }

setoid : (S : Setoid a ℓ) →
         (B → Setoid.Carrier S) →
         Setoid _ _
setoid S f = record
  { isEquivalence = isEquivalence f (Setoid.isEquivalence S)
  }

decSetoid : (D : DecSetoid a ℓ) →
            (B → DecSetoid.Carrier D) →
            DecSetoid _ _
decSetoid D f = record
  { isDecEquivalence = isDecEquivalence f (DecSetoid.isDecEquivalence D)
  }

poset : ∀ (P : Poset a ℓ₁ ℓ₂) →
        (B → Poset.Carrier P) →
        Poset _ _ _
poset P f = record
  { isPartialOrder = isPartialOrder f (Poset.isPartialOrder P)
  }

decPoset : (D : DecPoset a ℓ₁ ℓ₂) →
           (B → DecPoset.Carrier D) →
           DecPoset _ _ _
decPoset D f = record
  { isDecPartialOrder =
      isDecPartialOrder f (DecPoset.isDecPartialOrder D)
  }

strictPartialOrder : (S : StrictPartialOrder a ℓ₁ ℓ₂) →
                     (B → StrictPartialOrder.Carrier S) →
                     StrictPartialOrder _ _ _
strictPartialOrder S f = record
  { isStrictPartialOrder =
      isStrictPartialOrder f (StrictPartialOrder.isStrictPartialOrder S)
  }

totalOrder : (T : TotalOrder a ℓ₁ ℓ₂) →
             (B → TotalOrder.Carrier T) →
             TotalOrder _ _ _
totalOrder T f = record
  { isTotalOrder = isTotalOrder f (TotalOrder.isTotalOrder T)
  }

decTotalOrder : (D : DecTotalOrder a ℓ₁ ℓ₂) →
                (B → DecTotalOrder.Carrier D) →
                DecTotalOrder _ _ _
decTotalOrder D f = record
  { isDecTotalOrder = isDecTotalOrder f (DecTotalOrder.isDecTotalOrder D)
  }

strictTotalOrder : (S : StrictTotalOrder a ℓ₁ ℓ₂) →
                   (B → StrictTotalOrder.Carrier S) →
                   StrictTotalOrder _ _ _
strictTotalOrder S f = record
  { isStrictTotalOrder =
      isStrictTotalOrder f (StrictTotalOrder.isStrictTotalOrder S)
  }
