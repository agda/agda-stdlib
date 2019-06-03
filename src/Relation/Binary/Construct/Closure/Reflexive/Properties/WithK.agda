------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of reflexive closures which rely on the K rule
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Relation.Binary.Construct.Closure.Reflexive.Properties.WithK where

open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Sum as Sum
open import Relation.Binary
open import Relation.Binary.Construct.Closure.Reflexive
open import Relation.Binary.Construct.Closure.Reflexive.Properties public
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} where
  irrel : Irrelevant _~_ → Irreflexive _≡_ _~_ → Irrelevant (Refl _~_)
  irrel ~-irrel _        [ x∼y ] [ x∼y′ ] = PropEq.cong [_] (~-irrel x∼y x∼y′)
  irrel _       ~-irrefl [ x∼y ] refl     = ⊥-elim (~-irrefl refl x∼y)
  irrel _       ~-irrefl refl    [ x∼y ]  = ⊥-elim (~-irrefl refl x∼y)
  irrel _       _        refl    refl     = refl

  antisym : ∀ {ℓ'} {_≈_ : Rel _ ℓ'} → Reflexive _≈_ → Asymmetric _~_ → Antisymmetric _≈_ (Refl _~_)
  antisym ≈-refl ~-asym [ x∼y ] [ x∼y′ ] = ⊥-elim (~-asym x∼y x∼y′)
  antisym ≈-refl _      _       refl     = ≈-refl
  antisym ≈-refl _      refl    _        = ≈-refl

  isPreorder : Transitive _~_ → IsPreorder _≡_ (Refl _~_)
  isPreorder ~-trans = record
      { isEquivalence = PropEq.isEquivalence
      ; reflexive = λ { refl → refl }
      ; trans = trans ~-trans
      }

  isPartialOrder : IsStrictPartialOrder _≡_ _~_ → IsPartialOrder _≡_ (Refl _~_)
  isPartialOrder ~-IsStrictPartialOrder = record
      { isPreorder = isPreorder (IsStrictPartialOrder.trans ~-IsStrictPartialOrder)
      ; antisym = antisym {_} {_≡_} Eq.refl asym
      }
    where open IsStrictPartialOrder ~-IsStrictPartialOrder

  isDecPartialOrder : IsDecStrictPartialOrder _≡_ _~_ → IsDecPartialOrder _≡_ (Refl _~_)
  isDecPartialOrder ~-IsDecStrictPartialOrder = record
    { isPartialOrder = isPartialOrder isStrictPartialOrder
    ; _≟_ = _≟_
    ; _≤?_ = dec _≟_ _<?_
    }
    where open IsDecStrictPartialOrder ~-IsDecStrictPartialOrder

  total : Trichotomous _≡_ _~_ → Total (Refl _~_)
  total compare x y with compare x y
  ... | tri< a _    _ = inj₁ [ a ]
  ... | tri≈ _ refl _ = inj₁ refl
  ... | tri> _ _    c = inj₂ [ c ]

  isTotalOrder : IsStrictTotalOrder _≡_ _~_ → IsTotalOrder _≡_ (Refl _~_)
  isTotalOrder ~-IsStrictTotalOrder = record
    { isPartialOrder = isPartialOrder isStrictPartialOrder
    ; total = total compare
    } where
      open IsStrictTotalOrder ~-IsStrictTotalOrder

  isDecTotalOrder : IsStrictTotalOrder _≡_ _~_ → IsDecTotalOrder _≡_ (Refl _~_)
  isDecTotalOrder ~-IsStrictTotalOrder = record
    { isTotalOrder = isTotalOrder ~-IsStrictTotalOrder
    ; _≟_ = _≟_
    ; _≤?_ = dec _≟_ _<?_
    }
    where open IsStrictTotalOrder ~-IsStrictTotalOrder
