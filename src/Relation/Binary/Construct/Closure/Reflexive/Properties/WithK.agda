------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of reflexive closures which rely on the K rule
------------------------------------------------------------------------

{-# OPTIONS --safe --with-K #-}

module Relation.Binary.Construct.Closure.Reflexive.Properties.WithK where

open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Product as Prod
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

  antisym : ∀ {ℓ'} → (E : Σ (Rel A ℓ') Reflexive) → Asymmetric _~_ → Antisymmetric (proj₁ E) (Refl _~_)
  antisym _ ~-asym [ x∼y ] [ x∼y′ ] = ⊥-elim (~-asym x∼y x∼y′)
  antisym E _      _       refl     = proj₂ E
  antisym E _      refl    _        = proj₂ E

  total : Trichotomous _≡_ _~_ → Total (Refl _~_)
  total compare x y with compare x y
  ... | tri< a _    _ = inj₁ [ a ]
  ... | tri≈ _ refl _ = inj₁ refl
  ... | tri> _ _    c = inj₂ [ c ]

  isPreorder : Transitive _~_ → IsPreorder _≡_ (Refl _~_)
  isPreorder ~-trans = record
    { isEquivalence = PropEq.isEquivalence
    ; reflexive     = λ { refl → refl }
    ; trans         = trans ~-trans
    }

  isPartialOrder : IsStrictPartialOrder _≡_ _~_ → IsPartialOrder _≡_ (Refl _~_)
  isPartialOrder SPO = record
    { isPreorder = isPreorder (IsStrictPartialOrder.trans SPO)
    ; antisym    = antisym (_≡_ , refl) asym
    } where open IsStrictPartialOrder SPO

  isDecPartialOrder : IsDecStrictPartialOrder _≡_ _~_ → IsDecPartialOrder _≡_ (Refl _~_)
  isDecPartialOrder DSPO = record
    { isPartialOrder = isPartialOrder isStrictPartialOrder
    ; _≟_            = _≟_
    ; _≤?_           = dec _≟_ _<?_
    } where open IsDecStrictPartialOrder DSPO

  isTotalOrder : IsStrictTotalOrder _≡_ _~_ → IsTotalOrder _≡_ (Refl _~_)
  isTotalOrder STO = record
    { isPartialOrder = isPartialOrder isStrictPartialOrder
    ; total          = total compare
    } where open IsStrictTotalOrder STO

  isDecTotalOrder : IsStrictTotalOrder _≡_ _~_ → IsDecTotalOrder _≡_ (Refl _~_)
  isDecTotalOrder STO = record
    { isTotalOrder = isTotalOrder STO
    ; _≟_          = _≟_
    ; _≤?_         = dec _≟_ _<?_
    } where open IsStrictTotalOrder STO
