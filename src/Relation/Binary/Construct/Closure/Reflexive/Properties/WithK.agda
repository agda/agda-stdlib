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
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl)

module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} where
    irrel∧irrefl⟶irrel : Irrelevant _~_ → Irreflexive _≡_ _~_ → Irrelevant (Refl _~_)
    irrel∧irrefl⟶irrel ~-irrel _ [ x∼y ] [ x∼y′ ] = PropEq.cong [_] (~-irrel x∼y x∼y′)
    irrel∧irrefl⟶irrel _ ~-irrefl [ x∼y ] refl = ⊥-elim (~-irrefl refl x∼y)
    irrel∧irrefl⟶irrel _ ~-irrefl refl [ x∼y ] = ⊥-elim (~-irrefl refl x∼y)
    irrel∧irrefl⟶irrel _ _ refl refl = refl

    asym⟶antisym : ∀ {ℓ'} {_≈_ : Rel _ ℓ'} → Reflexive _≈_ → Asymmetric _~_ → Antisymmetric _≈_ (Refl _~_)
    asym⟶antisym ≈-refl ~-asym [ x∼y ] [ x∼y′ ] = ⊥-elim (~-asym x∼y x∼y′)
    asym⟶antisym ≈-refl _ _ refl = ≈-refl
    asym⟶antisym ≈-refl _ refl _ = ≈-refl

    preorder : Transitive _~_ → IsPreorder _≡_ (Refl _~_)
    preorder ~-trans = record
        { isEquivalence = PropEq.isEquivalence
        ; reflexive = λ { refl → refl }
        ; trans = trans ~-trans }

    partialOrder : IsStrictPartialOrder _≡_ _~_ → IsPartialOrder _≡_ (Refl _~_)
    partialOrder ~-IsStrictPartialOrder = record
        { isPreorder = preorder (IsStrictPartialOrder.trans ~-IsStrictPartialOrder)
        ; antisym = asym⟶antisym {_} {_≡_} Eq.refl asym }
      where open IsStrictPartialOrder ~-IsStrictPartialOrder

    decPartialOrder : IsDecStrictPartialOrder _≡_ _~_ → IsDecPartialOrder _≡_ (Refl _~_)
    decPartialOrder ~-IsDecStrictPartialOrder = record
      { isPartialOrder = partialOrder isStrictPartialOrder; _≟_ = _≟_; _≤?_ = dec _≟_ _<?_ }
      where open IsDecStrictPartialOrder ~-IsDecStrictPartialOrder

    totalOrder : IsStrictTotalOrder _≡_ _~_ → IsTotalOrder _≡_ (Refl _~_)
    totalOrder ~-IsStrictTotalOrder = record
      { isPartialOrder = partialOrder isStrictPartialOrder; total = total }
      where open IsStrictTotalOrder ~-IsStrictTotalOrder

            total : Total (Refl _~_)
            total x y with compare x y
            total _ _ | tri< a _ _ = inj₁ [ a ]
            total _ _ | tri≈ _ refl _ = inj₁ refl
            total _ _ | tri> _ _ c = inj₂ [ c ]

    decTotalOrder : IsStrictTotalOrder _≡_ _~_ → IsDecTotalOrder _≡_ (Refl _~_)
    decTotalOrder ~-IsStrictTotalOrder = record
      { isTotalOrder = totalOrder ~-IsStrictTotalOrder; _≟_ = _≟_; _≤?_ = dec _≟_ _<?_ }
      where open IsStrictTotalOrder ~-IsStrictTotalOrder
