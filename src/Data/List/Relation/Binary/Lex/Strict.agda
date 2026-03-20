------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of lists
------------------------------------------------------------------------

-- The definitions of lexicographic ordering used here are suitable if
-- the argument order is a strict partial order.

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Lex.Strict where

open import Function.Base using (_∘_; id)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.List.Base using (List; []; _∷_)
open import Level using (_⊔_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles
  using (StrictPartialOrder; StrictTotalOrder; Preorder; Poset; DecPoset; DecTotalOrder)
open import Relation.Binary.Structures
  using (IsEquivalence; IsStrictPartialOrder; IsStrictTotalOrder; IsPreorder; IsPartialOrder; IsDecPartialOrder; IsTotalOrder; IsDecTotalOrder)
open import Relation.Binary.Definitions
  using (Irreflexive; Symmetric; _Respects₂_; Total; Asymmetric; Antisymmetric; Transitive; Trichotomous; Decidable; tri≈; tri<; tri>)
open import Relation.Binary.Consequences
open import Data.List.Relation.Binary.Pointwise as Pointwise
   using (Pointwise; []; _∷_; head; tail)

import Data.List.Relation.Binary.Lex as Core

------------------------------------------------------------------------
-- Re-exporting core definitions

open Core public
  using (Lex-<; Lex-≤; base; halt; this; next; ¬≤-this; ¬≤-next)

------------------------------------------------------------------------
-- Strict lexicographic ordering.

module _ {a ℓ₁ ℓ₂} {A : Set a} where

  -- Properties

  module _ {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} where

    private
      _≋_ = Pointwise _≈_
      _<_ = Lex-< _≈_ _≺_

    xs≮[] : ∀ {xs} → ¬ xs < []
    xs≮[] (base ())

    ¬[]<[] : ¬ [] < []
    ¬[]<[] = xs≮[]

    <-irreflexive : Irreflexive _≈_ _≺_ → Irreflexive _≋_ _<_
    <-irreflexive irr (x≈y ∷ xs≋ys) (this x<y)     = irr x≈y x<y
    <-irreflexive irr (x≈y ∷ xs≋ys) (next _ xs⊴ys) =
      <-irreflexive irr xs≋ys xs⊴ys

    <-asymmetric : Symmetric _≈_ → _≺_ Respects₂ _≈_ → Asymmetric _≺_ →
                   Asymmetric _<_
    <-asymmetric sym resp as = asym
      where
      irrefl : Irreflexive _≈_ _≺_
      irrefl = asym⇒irr resp sym as

      asym : Asymmetric _<_
      asym (base bot)       _                = bot
      asym (this x<y)       (this y<x)       = as x<y y<x
      asym (this x<y)       (next y≈x ys⊴xs) = irrefl (sym y≈x) x<y
      asym (next x≈y xs⊴ys) (this y<x)       = irrefl (sym x≈y) y<x
      asym (next x≈y xs⊴ys) (next y≈x ys⊴xs) = asym xs⊴ys ys⊴xs

    <-antisymmetric : Symmetric _≈_ → Irreflexive _≈_ _≺_ →
                      Asymmetric _≺_ → Antisymmetric _≋_ _<_
    <-antisymmetric = Core.antisymmetric

    <-transitive : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ →
                   Transitive _≺_ → Transitive _<_
    <-transitive = Core.transitive

    <-compare : Symmetric _≈_ → Trichotomous _≈_ _≺_ →
                Trichotomous _≋_ _<_
    <-compare sym tri []       []       = tri≈ ¬[]<[] []    ¬[]<[]
    <-compare sym tri []       (y ∷ ys) = tri< halt   (λ()) (λ())
    <-compare sym tri (x ∷ xs) []       = tri> (λ())  (λ()) halt
    <-compare sym tri (x ∷ xs) (y ∷ ys) with tri x y
    ... | tri< x<y x≉y y≮x =
          tri< (this x<y) (x≉y ∘ head) (¬≤-this (x≉y ∘ sym) y≮x)
    ... | tri> x≮y x≉y y<x =
          tri> (¬≤-this x≉y x≮y) (x≉y ∘ head) (this y<x)
    ... | tri≈ x≮y x≈y y≮x with <-compare sym tri xs ys
    ...   | tri< xs<ys xs≉ys ys≮xs =
            tri< (next x≈y xs<ys) (xs≉ys ∘ tail) (¬≤-next y≮x ys≮xs)
    ...   | tri≈ xs≮ys xs≈ys ys≮xs =
            tri≈ (¬≤-next x≮y xs≮ys) (x≈y ∷ xs≈ys) (¬≤-next y≮x ys≮xs)
    ...   | tri> xs≮ys xs≉ys ys<xs =
            tri> (¬≤-next x≮y xs≮ys) (xs≉ys ∘ tail) (next (sym x≈y) ys<xs)

    <-decidable : Decidable _≈_ → Decidable _≺_ → Decidable _<_
    <-decidable = Core.decidable (no id)

    <-respects₂ : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ →
                  _<_ Respects₂ _≋_
    <-respects₂ = Core.respects₂

    <-isStrictPartialOrder : IsStrictPartialOrder _≈_ _≺_ →
                             IsStrictPartialOrder _≋_ _<_
    <-isStrictPartialOrder spo = record
      { isEquivalence = Pointwise.isEquivalence isEquivalence
      ; irrefl        = <-irreflexive irrefl
      ; trans         = Core.transitive isEquivalence <-resp-≈ trans
      ; <-resp-≈      = Core.respects₂ isEquivalence <-resp-≈
      } where open IsStrictPartialOrder spo

    <-isStrictTotalOrder : IsStrictTotalOrder _≈_ _≺_ →
                           IsStrictTotalOrder _≋_ _<_
    <-isStrictTotalOrder sto = record
      { isStrictPartialOrder = <-isStrictPartialOrder isStrictPartialOrder
      ; compare              = <-compare Eq.sym compare
      } where open IsStrictTotalOrder sto

<-strictPartialOrder : ∀ {a ℓ₁ ℓ₂} → StrictPartialOrder a ℓ₁ ℓ₂ →
                       StrictPartialOrder _ _ _
<-strictPartialOrder spo = record
  { isStrictPartialOrder = <-isStrictPartialOrder isStrictPartialOrder
  } where open StrictPartialOrder spo

<-strictTotalOrder : ∀ {a ℓ₁ ℓ₂} → StrictTotalOrder a ℓ₁ ℓ₂ →
                       StrictTotalOrder _ _ _
<-strictTotalOrder sto = record
  { isStrictTotalOrder = <-isStrictTotalOrder isStrictTotalOrder
  } where open StrictTotalOrder sto

------------------------------------------------------------------------
-- Non-strict lexicographic ordering.

module _ {a ℓ₁ ℓ₂} {A : Set a} where

  -- Properties

  ≤-reflexive : (_≈_ : Rel A ℓ₁) (_≺_ : Rel A ℓ₂) →
                Pointwise _≈_ ⇒ Lex-≤ _≈_ _≺_
  ≤-reflexive _≈_ _≺_ []            = base _
  ≤-reflexive _≈_ _≺_ (x≈y ∷ xs≈ys) =
    next x≈y (≤-reflexive _≈_ _≺_ xs≈ys)

  module _ {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} where

    private
      _≋_ = Pointwise _≈_
      _≤_ = Lex-≤ _≈_ _≺_

    ≤-antisymmetric : Symmetric _≈_ → Irreflexive _≈_ _≺_ →
                      Asymmetric _≺_ → Antisymmetric _≋_ _≤_
    ≤-antisymmetric = Core.antisymmetric

    ≤-transitive : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ →
                   Transitive _≺_ → Transitive _≤_
    ≤-transitive = Core.transitive

    -- Note that trichotomy is an unnecessarily strong precondition for
    -- the following lemma.

    ≤-total : Symmetric _≈_ → Trichotomous _≈_ _≺_ → Total _≤_
    ≤-total _   _   []       []       = inj₁ (base _)
    ≤-total _   _   []       (x ∷ xs) = inj₁ halt
    ≤-total _   _   (x ∷ xs) []       = inj₂ halt
    ≤-total sym tri (x ∷ xs) (y ∷ ys) with tri x y
    ... | tri< x<y _ _ = inj₁ (this x<y)
    ... | tri> _ _ y<x = inj₂ (this y<x)
    ... | tri≈ _ x≈y _ with ≤-total sym tri xs ys
    ...   | inj₁ xs≲ys = inj₁ (next      x≈y  xs≲ys)
    ...   | inj₂ ys≲xs = inj₂ (next (sym x≈y) ys≲xs)

    ≤-decidable : Decidable _≈_ → Decidable _≺_ → Decidable _≤_
    ≤-decidable = Core.decidable (yes _)

    ≤-respects₂ : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ →
                  _≤_ Respects₂ _≋_
    ≤-respects₂ = Core.respects₂

    ≤-isPreorder : IsEquivalence _≈_ → Transitive _≺_ →
                   _≺_ Respects₂ _≈_ → IsPreorder _≋_ _≤_
    ≤-isPreorder eq tr resp = record
      { isEquivalence = Pointwise.isEquivalence eq
      ; reflexive     = ≤-reflexive _≈_ _≺_
      ; trans         = Core.transitive eq resp tr
      }

    ≤-isPartialOrder : IsStrictPartialOrder _≈_ _≺_ →
                       IsPartialOrder _≋_ _≤_
    ≤-isPartialOrder  spo = record
      { isPreorder = ≤-isPreorder isEquivalence trans <-resp-≈
      ; antisym    = Core.antisymmetric Eq.sym irrefl asym
      }
      where open IsStrictPartialOrder spo

    ≤-isDecPartialOrder : IsStrictTotalOrder _≈_ _≺_ →
                          IsDecPartialOrder _≋_ _≤_
    ≤-isDecPartialOrder sto = record
      { isPartialOrder = ≤-isPartialOrder isStrictPartialOrder
      ; _≟_            = Pointwise.decidable _≟_
      ; _≤?_           = ≤-decidable _≟_ _<?_
      } where open IsStrictTotalOrder sto

    ≤-isTotalOrder : IsStrictTotalOrder _≈_ _≺_ → IsTotalOrder _≋_ _≤_
    ≤-isTotalOrder sto = record
      { isPartialOrder = ≤-isPartialOrder isStrictPartialOrder
      ; total          = ≤-total Eq.sym compare
      }
      where open IsStrictTotalOrder sto

    ≤-isDecTotalOrder : IsStrictTotalOrder _≈_ _≺_ →
                        IsDecTotalOrder _≋_ _≤_
    ≤-isDecTotalOrder sto = record
      { isTotalOrder = ≤-isTotalOrder sto
      ; _≟_          = Pointwise.decidable _≟_
      ; _≤?_         = ≤-decidable _≟_ _<?_
      }
      where open IsStrictTotalOrder sto

≤-preorder : ∀ {a ℓ₁ ℓ₂} → Preorder a ℓ₁ ℓ₂ → Preorder _ _ _
≤-preorder pre = record
  { isPreorder = ≤-isPreorder isEquivalence trans ∼-resp-≈
  } where open Preorder pre

≤-partialOrder : ∀ {a ℓ₁ ℓ₂} → StrictPartialOrder a ℓ₁ ℓ₂ → Poset _ _ _
≤-partialOrder spo = record
  { isPartialOrder = ≤-isPartialOrder isStrictPartialOrder
  } where open StrictPartialOrder spo

≤-decPoset : ∀ {a ℓ₁ ℓ₂} → StrictTotalOrder a ℓ₁ ℓ₂ →
             DecPoset _ _ _
≤-decPoset sto = record
  { isDecPartialOrder = ≤-isDecPartialOrder isStrictTotalOrder
  } where open StrictTotalOrder sto


≤-decTotalOrder : ∀ {a ℓ₁ ℓ₂} → StrictTotalOrder a ℓ₁ ℓ₂ →
                  DecTotalOrder _ _ _
≤-decTotalOrder sto = record
  { isDecTotalOrder = ≤-isDecTotalOrder isStrictTotalOrder
  } where open StrictTotalOrder sto
