------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of same-length vector
------------------------------------------------------------------------

-- The definitions of lexicographic orderings used here is suitable if
-- the argument order is a (non-strict) partial order.

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Relation.Binary.Lex.NonStrict where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (Vec; []; _∷_)
import Data.Vec.Relation.Binary.Lex.Strict as Strict
open import Data.Vec.Relation.Binary.Pointwise.Inductive as Pointwise
  using (Pointwise; []; _∷_; head; tail)
open import Function.Base using (id)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (REL; Rel; _⇒_)
open import Relation.Binary.Bundles
  using (Poset; StrictPartialOrder; DecPoset; DecStrictPartialOrder
        ; DecTotalOrder; StrictTotalOrder; Preorder; TotalOrder)
open import Relation.Binary.Structures
  using (IsEquivalence; IsPartialOrder; IsStrictPartialOrder; IsDecPartialOrder
        ; IsDecStrictPartialOrder; IsDecTotalOrder; IsStrictTotalOrder
        ; IsPreorder; IsTotalOrder)
open import Relation.Binary.Definitions
  using (Irreflexive; _Respects₂_; Antisymmetric; Asymmetric; Symmetric; Trans
        ; Decidable; Total; Trichotomous)
import Relation.Binary.Construct.NonStrictToStrict as Conv
open import Relation.Nullary.Decidable.Core using (yes; no)

private
  variable
    a ℓ₁ ℓ₂ : Level
    A : Set a

------------------------------------------------------------------------
-- Publicly re-export definitions from Core
------------------------------------------------------------------------

open import Data.Vec.Relation.Binary.Lex.Core as Core public
  using (base; this; next; ≰-this; ≰-next)

------------------------------------------------------------------------
-- Definitions
------------------------------------------------------------------------

module _ {A : Set a} (_≈_ : Rel A ℓ₁) (_≼_ : Rel A ℓ₂) where

  Lex-< : ∀ {m n} → REL (Vec A m) (Vec A n) (a ⊔ ℓ₁ ⊔ ℓ₂)
  Lex-< = Core.Lex {A = A} ⊥ _≈_ (Conv._<_ _≈_ _≼_)

  Lex-≤ : ∀ {m n} → REL (Vec A m) (Vec A n) (a ⊔ ℓ₁ ⊔ ℓ₂)
  Lex-≤ = Core.Lex {A = A} ⊤ _≈_ (Conv._<_ _≈_ _≼_)

------------------------------------------------------------------------
-- Properties of Lex-<
------------------------------------------------------------------------

module _ {_≈_ : Rel A ℓ₁} {_≼_ : Rel A ℓ₂} where

  private
    _≋_ = Pointwise _≈_
    _<_ = Lex-< _≈_ _≼_

  <-irrefl : ∀ {m n} → Irreflexive (_≋_ {m} {n}) _<_
  <-irrefl = Strict.<-irrefl (Conv.<-irrefl _≈_ _≼_)

  <-asym : IsEquivalence _≈_ → _≼_ Respects₂ _≈_ → Antisymmetric _≈_ _≼_ →
           ∀ {n} → Asymmetric (_<_ {n} {n})
  <-asym ≈-equiv ≼-resp-≈ ≼-antisym = Strict.<-asym sym
    (Conv.<-resp-≈ _ _ ≈-equiv ≼-resp-≈)
    (Conv.<-asym _≈_ _ ≼-antisym)
    where open IsEquivalence ≈-equiv

  <-antisym : Symmetric _≈_ → Antisymmetric _≈_ _≼_ →
              ∀ {n} → Antisymmetric (_≋_ {n} {n}) _<_
  <-antisym ≈-sym ≼-antisym = Core.antisym ≈-sym
    (Conv.<-irrefl _≈_ _≼_)
    (Conv.<-asym _≈_ _≼_ ≼-antisym)

  <-trans : IsPartialOrder _≈_ _≼_ →
            ∀ {m n o} → Trans (_<_ {m} {n}) (_<_ {n} {o}) _<_
  <-trans ≼-isPartialOrder = Core.transitive Eq.isPartialEquivalence
    (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈)
    (Conv.<-trans _ _ ≼-isPartialOrder)
    where open IsPartialOrder ≼-isPartialOrder

  <-resp₂ : IsEquivalence _≈_ → _≼_ Respects₂ _≈_ →
            ∀ {n} → _Respects₂_ (_<_ {n} {n}) _≋_
  <-resp₂ ≈-equiv ≼-resp-≈ = Core.respects₂
    (IsEquivalence.isPartialEquivalence ≈-equiv)
    (Conv.<-resp-≈ _ _ ≈-equiv ≼-resp-≈)

  <-cmp : Symmetric _≈_ → Decidable _≈_ → Antisymmetric _≈_ _≼_ → Total _≼_ →
          ∀ {n} → Trichotomous (_≋_ {n} {n}) _<_
  <-cmp ≈-sym _≟_ ≼-antisym ≼-total = Strict.<-cmp ≈-sym
    (Conv.<-trichotomous _ _ ≈-sym _≟_ ≼-antisym ≼-total)

  _<?_ : Decidable _≈_ → Decidable _≼_ → ∀ {m n} → Decidable (_<_ {m} {n})
  _<?_ _≟_ _≼?_ = Core.decidable (no id) _≟_
    (Conv.<-decidable _ _ _≟_ _≼?_)

------------------------------------------------------------------------
-- Structures

  <-isStrictPartialOrder : IsPartialOrder _≈_ _≼_ →
                           ∀ {n} → IsStrictPartialOrder (_≋_ {n} {n}) _<_
  <-isStrictPartialOrder ≼-isPartialOrder {n} = Strict.<-isStrictPartialOrder
    (Conv.<-isStrictPartialOrder _ _ ≼-isPartialOrder)

  <-isDecStrictPartialOrder : IsDecPartialOrder _≈_ _≼_ →
                              ∀ {n} → IsDecStrictPartialOrder (_≋_ {n} {n}) _<_
  <-isDecStrictPartialOrder ≼-isDecPartialOrder {n} = Strict.<-isDecStrictPartialOrder
    (Conv.<-isDecStrictPartialOrder _ _ ≼-isDecPartialOrder)

  <-isStrictTotalOrder : IsDecTotalOrder _≈_ _≼_ →
                         ∀ {n} → IsStrictTotalOrder (_≋_ {n} {n}) _<_
  <-isStrictTotalOrder ≼-isDecTotalOrder {n} = Strict.<-isStrictTotalOrder
    (Conv.<-isStrictTotalOrder₂ _ _ ≼-isDecTotalOrder)

------------------------------------------------------------------------
-- Bundles

<-strictPartialOrder : Poset a ℓ₁ ℓ₂ → ℕ → StrictPartialOrder _ _ _
<-strictPartialOrder ≼-po n = record
  { isStrictPartialOrder = <-isStrictPartialOrder isPartialOrder {n = n}
  } where open Poset ≼-po

<-decStrictPartialOrder : DecPoset a ℓ₁ ℓ₂ → ℕ → DecStrictPartialOrder _ _ _
<-decStrictPartialOrder ≼-dpo n = record
  { isDecStrictPartialOrder = <-isDecStrictPartialOrder isDecPartialOrder {n = n}
  } where open DecPoset ≼-dpo

<-strictTotalOrder : DecTotalOrder a ℓ₁ ℓ₂ → ℕ → StrictTotalOrder _ _ _
<-strictTotalOrder ≼-dto n = record
  { isStrictTotalOrder = <-isStrictTotalOrder isDecTotalOrder {n = n}
  } where open DecTotalOrder ≼-dto

------------------------------------------------------------------------
-- Properties of Lex-≤
------------------------------------------------------------------------

module _ {_≈_ : Rel A ℓ₁} {_≼_ : Rel A ℓ₂} where

  private
    _≋_ = Pointwise _≈_
    _<_ = Lex-< _≈_ _≼_
    _≤_ = Lex-≤ _≈_ _≼_

  <⇒≤ : ∀ {m n} {xs : Vec A m} {ys : Vec A n} → xs < ys → xs ≤ ys
  <⇒≤ = Core.map-P ⊥-elim

  ≤-refl : ∀ {m n} → (_≋_ {m} {n}) ⇒ _≤_
  ≤-refl = Strict.≤-refl

  ≤-antisym : Symmetric _≈_ → Antisymmetric _≈_ _≼_ →
              ∀ {n} → Antisymmetric (_≋_ {n} {n}) _≤_
  ≤-antisym ≈-sym ≼-antisym = Core.antisym ≈-sym
    (Conv.<-irrefl _≈_ _≼_)
    (Conv.<-asym _ _≼_ ≼-antisym)

  private
    trans : IsPartialOrder _≈_ _≼_ → ∀ {P₁ P₂} {m n o} →
            Trans (Core.Lex P₁ _≈_ (Conv._<_ _≈_ _≼_) {m} {n}) (Core.Lex P₂ _≈_ (Conv._<_ _≈_ _≼_) {n} {o}) _
    trans ≼-po = Core.transitive′
      (IsEquivalence.isPartialEquivalence isEquivalence)
      (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈)
      (Conv.<-trans _ _≼_ ≼-po)
      where open IsPartialOrder ≼-po

  ≤-trans : IsPartialOrder _≈_ _≼_ → ∀ {m n o} → Trans (_≤_ {m} {n}) (_≤_ {n} {o}) _≤_
  ≤-trans ≼-po xs≤ys ys≤zs = Core.map-P proj₁ (trans ≼-po xs≤ys ys≤zs)

  <-transʳ : IsPartialOrder _≈_ _≼_ → ∀ {m n o} → Trans (_≤_ {m} {n}) (_<_ {n} {o}) _<_
  <-transʳ ≼-po xs≤ys ys<zs = Core.map-P proj₂ (trans ≼-po xs≤ys ys<zs)

  <-transˡ : IsPartialOrder _≈_ _≼_ → ∀ {m n o} → Trans (_<_ {m} {n}) (_≤_ {n} {o}) _<_
  <-transˡ ≼-po xs<ys ys≤zs = Core.map-P proj₁ (trans ≼-po xs<ys ys≤zs)

  ≤-total : Symmetric _≈_ → Decidable _≈_ → Antisymmetric _≈_ _≼_ → Total _≼_ →
            ∀ {n} → Total (_≤_ {n})
  ≤-total ≈-sym _≟_ ≼-antisym ≼-total = Strict.≤-total ≈-sym
    (Conv.<-trichotomous _ _ ≈-sym _≟_ ≼-antisym ≼-total)

  _≤?_ : Decidable _≈_ → Decidable _≼_ →
          ∀ {m n} → Decidable (_≤_ {m} {n})
  _≤?_ _≟_ _≼?_ = Core.decidable (yes tt) _≟_
    (Conv.<-decidable _ _ _≟_ _≼?_)

  ≤-resp₂ : IsEquivalence _≈_ → _≼_ Respects₂ _≈_ →
            ∀ {n} → _Respects₂_ (_≤_ {n} {n}) _≋_
  ≤-resp₂ ≈-equiv ≼-resp-≈ = Core.respects₂
    (IsEquivalence.isPartialEquivalence ≈-equiv)
    (Conv.<-resp-≈ _ _ ≈-equiv ≼-resp-≈)

------------------------------------------------------------------------
-- Structures

  ≤-isPreorder : IsPartialOrder _≈_ _≼_ →
                 ∀ {n} → IsPreorder (_≋_ {n} {n}) _≤_
  ≤-isPreorder ≼-po = Strict.≤-isPreorder isEquivalence (Conv.<-trans _ _ ≼-po) (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈)
    where open IsPartialOrder ≼-po

  ≤-isPartialOrder : IsPartialOrder _≈_ _≼_ →
                     ∀ {n} → IsPartialOrder (_≋_ {n} {n}) _≤_
  ≤-isPartialOrder ≼-po = Strict.≤-isPartialOrder (Conv.<-isStrictPartialOrder _ _ ≼-po)

  ≤-isDecPartialOrder : IsDecPartialOrder _≈_ _≼_ →
                        ∀ {n} → IsDecPartialOrder (_≋_ {n} {n}) _≤_
  ≤-isDecPartialOrder ≼-dpo = Strict.≤-isDecPartialOrder (Conv.<-isDecStrictPartialOrder _ _ ≼-dpo)

  ≤-isTotalOrder : Decidable _≈_ → IsTotalOrder _≈_ _≼_ →
                   ∀ {n} → IsTotalOrder (_≋_ {n} {n}) _≤_
  ≤-isTotalOrder _≟_ ≼-isTotalOrder = Strict.≤-isTotalOrder (Conv.<-isStrictTotalOrder₁ _ _ _≟_ ≼-isTotalOrder)

  ≤-isDecTotalOrder : IsDecTotalOrder _≈_ _≼_ →
                      ∀ {n} → IsDecTotalOrder (_≋_ {n} {n}) _≤_
  ≤-isDecTotalOrder ≼-isDecTotalOrder  = Strict.≤-isDecTotalOrder (Conv.<-isStrictTotalOrder₂ _ _ ≼-isDecTotalOrder)

------------------------------------------------------------------------
-- Bundles

≤-preorder : Poset a ℓ₁ ℓ₂ → ℕ → Preorder _ _ _
≤-preorder ≼-po n = record
  { isPreorder = ≤-isPreorder isPartialOrder {n = n}
  } where open Poset ≼-po

≤-poset : Poset a ℓ₁ ℓ₂ → ℕ → Poset _ _ _
≤-poset ≼-po n = record
  { isPartialOrder = ≤-isPartialOrder isPartialOrder {n = n}
  } where open Poset ≼-po

≤-decPoset : DecPoset a ℓ₁ ℓ₂ → ℕ → DecPoset _ _ _
≤-decPoset ≼-dpo n = record
  { isDecPartialOrder = ≤-isDecPartialOrder isDecPartialOrder {n = n}
  } where open DecPoset ≼-dpo

≤-totalOrder : (≼-dto : TotalOrder a ℓ₁ ℓ₂) → Decidable (TotalOrder._≈_ ≼-dto) → ℕ → TotalOrder _ _ _
≤-totalOrder ≼-dto _≟_ n = record
  { isTotalOrder = ≤-isTotalOrder _≟_ isTotalOrder {n = n}
  } where open TotalOrder ≼-dto

≤-decTotalOrder : DecTotalOrder a ℓ₁ ℓ₂ → ℕ → DecTotalOrder _ _ _
≤-decTotalOrder ≼-dto n = record
  { isDecTotalOrder = ≤-isDecTotalOrder isDecTotalOrder {n = n}
  } where open DecTotalOrder ≼-dto

------------------------------------------------------------------------
-- Reasoning
------------------------------------------------------------------------

module ≤-Reasoning  {_≈_ : Rel A ℓ₁} {_≼_ : Rel A ℓ₂}
                    (≼-po : IsPartialOrder _≈_ _≼_)
                    (n : ℕ)
                    where

  open IsPartialOrder ≼-po

  open import Relation.Binary.Reasoning.Base.Triple
    (≤-isPreorder ≼-po {n})
    (<-asym isEquivalence ≤-resp-≈ antisym)
    (<-trans ≼-po)
    (<-resp₂ isEquivalence ≤-resp-≈)
    <⇒≤
    (<-transˡ ≼-po)
    (<-transʳ ≼-po)
    public


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.4

<-dec = _<?_
{-# WARNING_ON_USAGE <-dec
"Warning: <-dec was deprecated in v2.4.
Please use _<?_ instead."
#-}

≤-dec = _≤?_
{-# WARNING_ON_USAGE ≤-dec
"Warning: ≤-dec was deprecated in v2.4.
Please use _≤?_ instead."
#-}
