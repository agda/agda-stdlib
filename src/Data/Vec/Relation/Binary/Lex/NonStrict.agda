------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of vector
------------------------------------------------------------------------

-- The definitions of lexicographic orderings used here is suitable if
-- the argument order is a (non-strict) partial order.

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Relation.Binary.Lex.NonStrict where

open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Product using (proj₁; proj₂)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)
import Data.Vec.Relation.Binary.Lex.Strict as Strict
open import Data.Vec.Relation.Binary.Pointwise.Inductive as Pointwise using (Pointwise; []; _∷_; head; tail)
open import Function using (id)
open import Relation.Binary
import Relation.Binary.Construct.NonStrictToStrict as Conv
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary hiding (Irrelevant)
open import Level using (_⊔_)

------------------------------------------------------------------------
-- Publicly re-export definitions from Core

open import Data.Vec.Relation.Binary.Lex.Core as Core public
  using (base; this; next; ¬≤-this; ¬≤-next)

----------------------------------------------------------------------
-- Strict lexicographic ordering.

module _ {a ℓ₁ ℓ₂} {A : Set a} where

  Lex-< : (_≈_ : Rel A ℓ₁) (_≺_ : Rel A ℓ₂) → ∀ {m n} → REL (Vec A m) (Vec A n) (a ⊔ ℓ₁ ⊔ ℓ₂)
  Lex-< _≈_ _≼_ = Core.Lex ⊥ _≈_ (Conv._<_ _≈_ _≼_)

  -- Properties

  module _ {_≈_ : Rel A ℓ₁} {_≼_ : Rel A ℓ₂} where

    private
      _≋_ = Pointwise _≈_
      _<_ = Lex-< _≈_ _≼_

    Lex-<-irrefl : ∀ {m n} → Irreflexive (_≋_ {m} {n}) _<_
    Lex-<-irrefl = Strict.Lex-<-irrefl (Conv.<-irrefl _≈_ _≼_)

    Lex-<-asym : ∀ {n} → IsEquivalence _≈_ → _≼_ Respects₂ _≈_ → Antisymmetric _≈_ _≼_ → Asymmetric (_<_ {n} {n})
    Lex-<-asym ≈-equiv ≼-resp-≈ ≼-antisym = Strict.Lex-<-asym sym (Conv.<-resp-≈ _ _ ≈-equiv ≼-resp-≈) (Conv.<-asym _≈_ _ ≼-antisym) where
      open IsEquivalence ≈-equiv

    Lex-<-antisym : ∀ {n} → Symmetric _≈_ → Antisymmetric _≈_ _≼_ → Antisymmetric (_≋_ {n} {n}) _<_
    Lex-<-antisym ≈-sym ≼-antisym = Core.Lex-antisym ≈-sym (Conv.<-irrefl _≈_ _≼_) (Conv.<-asym _≈_ _≼_ ≼-antisym)

    Lex-<-trans : ∀ {m n o} → IsPartialOrder _≈_ _≼_ → Trans (_<_ {m} {n}) (_<_ {n} {o}) _<_
    Lex-<-trans ≼-isPartialOrder = Core.Lex-trans Eq.isPartialEquivalence (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈) (Conv.<-trans _ _ ≼-isPartialOrder) where
      open IsPartialOrder ≼-isPartialOrder

    Lex-<-resp₂ : ∀ {n} → IsEquivalence _≈_ → _≼_ Respects₂ _≈_ → _Respects₂_ (_<_ {n} {n}) _≋_
    Lex-<-resp₂ ≈-equiv ≼-resp-≈ = Core.Lex-respects₂ (IsEquivalence.isPartialEquivalence ≈-equiv) (Conv.<-resp-≈ _ _ ≈-equiv ≼-resp-≈)

    Lex-<-cmp : ∀ {n} → Symmetric _≈_ → Decidable _≈_ → Antisymmetric _≈_ _≼_ → Total _≼_ → Trichotomous (_≋_ {n} {n}) _<_
    Lex-<-cmp ≈-sym _≟_ ≼-antisym ≼-total = Strict.Lex-<-cmp ≈-sym (Conv.<-trichotomous _ _ ≈-sym _≟_ ≼-antisym ≼-total)

    Lex-<? : ∀ {m n} → Decidable _≈_ → Decidable _≼_ → Decidable (_<_ {m} {n})
    Lex-<? _≟_ _≼?_ = Core.Lex? (no id) _≟_ (Conv.<-decidable _ _ _≟_ _≼?_)

    Lex-<-isStrictPartialOrder : ∀ {n} → IsPartialOrder _≈_ _≼_ → IsStrictPartialOrder (_≋_ {n} {n}) _<_
    Lex-<-isStrictPartialOrder {n} ≼-isPartialOrder = Strict.Lex-<-isStrictPartialOrder (Conv.<-isStrictPartialOrder _ _ ≼-isPartialOrder)

    Lex-<-isDecStrictPartialOrder : ∀ {n} → IsDecPartialOrder _≈_ _≼_ → IsDecStrictPartialOrder (_≋_ {n} {n}) _<_
    Lex-<-isDecStrictPartialOrder {n} ≼-isDecPartialOrder = Strict.Lex-<-isDecStrictPartialOrder (Conv.<-isDecStrictPartialOrder _ _ ≼-isDecPartialOrder)

    Lex-<-isStrictTotalOrder : ∀ {n} → IsDecTotalOrder _≈_ _≼_ → IsStrictTotalOrder (_≋_ {n} {n}) _<_
    Lex-<-isStrictTotalOrder {n} ≼-isDecTotalOrder = Strict.Lex-<-isStrictTotalOrder (Conv.<-isStrictTotalOrder₂ _ _ ≼-isDecTotalOrder)

Lex-<-strictPartialOrder : ∀ {a ℓ₁ ℓ₂} → Poset a ℓ₁ ℓ₂ → ℕ → StrictPartialOrder _ _ _
Lex-<-strictPartialOrder ≼-po n = record
  { isStrictPartialOrder = Lex-<-isStrictPartialOrder {n = n} isPartialOrder
  } where open Poset ≼-po

Lex-<-decStrictPartialOrder : ∀ {a ℓ₁ ℓ₂} → DecPoset a ℓ₁ ℓ₂ → ℕ → DecStrictPartialOrder _ _ _
Lex-<-decStrictPartialOrder ≼-dpo n = record
  { isDecStrictPartialOrder = Lex-<-isDecStrictPartialOrder {n = n} isDecPartialOrder
  } where open DecPoset ≼-dpo

Lex-<-strictTotalOrder : ∀ {a ℓ₁ ℓ₂} → DecTotalOrder a ℓ₁ ℓ₂ → ℕ → StrictTotalOrder _ _ _
Lex-<-strictTotalOrder ≼-dto n = record
  { isStrictTotalOrder = Lex-<-isStrictTotalOrder {n = n} isDecTotalOrder
  } where open DecTotalOrder ≼-dto

------------------------------------------------------------------------
-- Non-strict lexicographic ordering.

module _ {a ℓ₁ ℓ₂} {A : Set a} where

  Lex-≤ : (_≈_ : Rel A ℓ₁) (_≺_ : Rel A ℓ₂) → ∀ {m n} → REL (Vec A m) (Vec A n) (a ⊔ ℓ₁ ⊔ ℓ₂)
  Lex-≤ _≈_ _≼_ = Core.Lex ⊤ _≈_ (Conv._<_ _≈_ _≼_)

  -- Properties
  module _ {_≈_ : Rel A ℓ₁} {_≼_ : Rel A ℓ₂} where

    private
      _≋_ = Pointwise _≈_
      _<_ = Lex-< _≈_ _≼_
      _≤_ = Lex-≤ _≈_ _≼_

    Lex-≤-refl : ∀ {m n} → (_≋_ {m} {n}) ⇒ _≤_
    Lex-≤-refl = Strict.Lex-≤-refl

    Lex-≤-antisym : ∀ {n} → Symmetric _≈_ → Antisymmetric _≈_ _≼_ → Antisymmetric (_≋_ {n} {n}) _≤_
    Lex-≤-antisym ≈-sym ≼-antisym = Core.Lex-antisym ≈-sym (Conv.<-irrefl _≈_ _≼_) (Conv.<-asym _ _≼_ ≼-antisym)

    private
      Lex-trans : ∀ {m n o P₁ P₂} → IsPartialOrder _≈_ _≼_ → Trans (Core.Lex P₁ _≈_ (Conv._<_ _≈_ _≼_) {m} {n}) (Core.Lex P₂ _≈_ (Conv._<_ _≈_ _≼_) {n} {o}) _
      Lex-trans ≼-po = Core.Lex-trans′ (IsEquivalence.isPartialEquivalence isEquivalence) (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈) (Conv.<-trans _ _≼_ ≼-po) where
        open IsPartialOrder ≼-po

    Lex-≤-trans : ∀ {m n o} → IsPartialOrder _≈_ _≼_ → Trans (_≤_ {m} {n}) (_≤_ {n} {o}) _≤_
    Lex-≤-trans ≼-po xs≤ys ys≤zs = Core.Lex-mapP proj₁ (Lex-trans ≼-po xs≤ys ys≤zs)

    Lex-<-transʳ : ∀ {m n o} → IsPartialOrder _≈_ _≼_ → Trans (_≤_ {m} {n}) (_<_ {n} {o}) _<_
    Lex-<-transʳ ≼-po xs≤ys ys<zs = Core.Lex-mapP proj₂ (Lex-trans ≼-po xs≤ys ys<zs)

    Lex-<-transˡ : ∀ {m n o} → IsPartialOrder _≈_ _≼_ → Trans (_<_ {m} {n}) (_≤_ {n} {o}) _<_
    Lex-<-transˡ ≼-po xs<ys ys≤zs = Core.Lex-mapP proj₁ (Lex-trans ≼-po xs<ys ys≤zs)

    Lex-≤-total : ∀ {n} → Symmetric _≈_ → Decidable _≈_ → Antisymmetric _≈_ _≼_ → Total _≼_ → Total (_≤_ {n})
    Lex-≤-total ≈-sym _≟_ ≼-antisym ≼-total = Strict.Lex-≤-total ≈-sym (Conv.<-trichotomous _ _ ≈-sym _≟_ ≼-antisym ≼-total)

    Lex-≤? : ∀ {m n} → Decidable _≈_ → Decidable _≼_ → Decidable (_≤_ {m} {n})
    Lex-≤? _≟_ _≼?_ = Core.Lex? (yes tt) _≟_ (Conv.<-decidable _ _ _≟_ _≼?_)

    Lex-≤-resp₂ : ∀ {n} → IsEquivalence _≈_ → _≼_ Respects₂ _≈_ → _Respects₂_ (_≤_ {n} {n}) _≋_
    Lex-≤-resp₂ ≈-equiv ≼-resp-≈ = Core.Lex-respects₂ (IsEquivalence.isPartialEquivalence ≈-equiv) (Conv.<-resp-≈ _ _ ≈-equiv ≼-resp-≈)

    Lex-≤-isPreorder : ∀ {n} → IsPartialOrder _≈_ _≼_ → IsPreorder (_≋_ {n} {n}) _≤_
    Lex-≤-isPreorder ≼-po = Strict.Lex-≤-isPreorder isEquivalence (Conv.<-trans _ _ ≼-po) (Conv.<-resp-≈ _ _ isEquivalence ≤-resp-≈) where
      open IsPartialOrder ≼-po

    Lex-≤-isPartialOrder : ∀ {n} → IsPartialOrder _≈_ _≼_ → IsPartialOrder (_≋_ {n} {n}) _≤_
    Lex-≤-isPartialOrder ≼-po = Strict.Lex-≤-isPartialOrder (Conv.<-isStrictPartialOrder _ _ ≼-po)

    Lex-≤-isDecPartialOrder : ∀ {n} → IsDecPartialOrder _≈_ _≼_ → IsDecPartialOrder (_≋_ {n} {n}) _≤_
    Lex-≤-isDecPartialOrder ≼-dpo = Strict.Lex-≤-isDecPartialOrder (Conv.<-isDecStrictPartialOrder _ _ ≼-dpo)

    Lex-≤-isTotalOrder : ∀ {n} → Decidable _≈_ → IsTotalOrder _≈_ _≼_ → IsTotalOrder (_≋_ {n} {n}) _≤_
    Lex-≤-isTotalOrder _≟_ ≼-isTotalOrder = Strict.Lex-≤-isTotalOrder (Conv.<-isStrictTotalOrder₁ _ _ _≟_ ≼-isTotalOrder)

    Lex-≤-isDecTotalOrder : ∀ {n} → IsDecTotalOrder _≈_ _≼_ → IsDecTotalOrder (_≋_ {n} {n}) _≤_
    Lex-≤-isDecTotalOrder ≼-isDecTotalOrder  = Strict.Lex-≤-isDecTotalOrder (Conv.<-isStrictTotalOrder₂ _ _ ≼-isDecTotalOrder)

    Lex-<⇒Lex-≤ : ∀ {m n} {xs : Vec A m} {ys : Vec A n} → xs < ys → xs ≤ ys
    Lex-<⇒Lex-≤ = Core.Lex-mapP ⊥-elim

    module ≤-Reasoning (≼-po : IsPartialOrder _≈_ _≼_) (n : ℕ) where
      open IsPartialOrder ≼-po
      open import Relation.Binary.Reasoning.Base.Triple
        (Lex-≤-isPreorder {n} ≼-po)
        (Lex-<-trans {m = n} {n = n} {o = n} ≼-po)
        (Lex-<-resp₂ isEquivalence ≤-resp-≈)
        Lex-<⇒Lex-≤
        (Lex-<-transˡ ≼-po)
        (Lex-<-transʳ ≼-po)
        public

Lex-≤-preorder : ∀ {a ℓ₁ ℓ₂} → Poset a ℓ₁ ℓ₂ → ℕ → Preorder _ _ _
Lex-≤-preorder ≼-po n = record
  { isPreorder = Lex-≤-isPreorder {n = n} isPartialOrder
  } where open Poset ≼-po

Lex-≤-poset : ∀ {a ℓ₁ ℓ₂} → Poset a ℓ₁ ℓ₂ → ℕ → Poset _ _ _
Lex-≤-poset ≼-po n = record
  { isPartialOrder = Lex-≤-isPartialOrder {n = n} isPartialOrder
  } where open Poset ≼-po

Lex-≤-decPoset : ∀ {a ℓ₁ ℓ₂} → DecPoset a ℓ₁ ℓ₂ → ℕ → DecPoset _ _ _
Lex-≤-decPoset ≼-dpo n = record
  { isDecPartialOrder = Lex-≤-isDecPartialOrder {n = n} isDecPartialOrder
  } where open DecPoset ≼-dpo

Lex-≤-totalOrder : ∀ {a ℓ₁ ℓ₂} →  (≼-dto : TotalOrder a ℓ₁ ℓ₂) → Decidable (TotalOrder._≈_ ≼-dto) → ℕ → TotalOrder _ _ _
Lex-≤-totalOrder ≼-dto _≟_ n = record
  { isTotalOrder = Lex-≤-isTotalOrder {n = n} _≟_ isTotalOrder
  } where open TotalOrder ≼-dto

Lex-≤-decTotalOrder : ∀ {a ℓ₁ ℓ₂} → DecTotalOrder a ℓ₁ ℓ₂ → ℕ → DecTotalOrder _ _ _
Lex-≤-decTotalOrder ≼-dto n = record
  { isDecTotalOrder = Lex-≤-isDecTotalOrder {n = n} isDecTotalOrder
  } where open DecTotalOrder ≼-dto

