------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of lists of same-length vectors
------------------------------------------------------------------------

-- The definitions of lexicographic ordering used here are suitable if
-- the argument order is a strict partial order.

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Relation.Binary.Lex.Strict where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Unit.Properties using (⊤-irrelevant)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as Pointwise
  using (Pointwise; []; _∷_; head; tail)
open import Function.Base using (id; _∘_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary
open import Relation.Binary.Consequences
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Level using (Level; _⊔_)

private
  variable
    a ℓ₁ ℓ₂ : Level
    A : Set a

----------------------------------------------------------------------
-- Re-exports
----------------------------------------------------------------------

open import Data.Vec.Relation.Binary.Lex.Core as Core public
  using (base; this; next; ≰-this; ≰-next)

----------------------------------------------------------------------
-- Definitions
----------------------------------------------------------------------

module _ {A : Set a} (_≈_ : Rel A ℓ₁) (_≺_ : Rel A ℓ₂) where

  Lex-< : ∀ {m n} → REL (Vec A m) (Vec A n) (a ⊔ ℓ₁ ⊔ ℓ₂)
  Lex-< = Core.Lex {A = A} ⊥ _≈_ _≺_

  Lex-≤ : ∀ {m n} → REL (Vec A m) (Vec A n) (a ⊔ ℓ₁ ⊔ ℓ₂)
  Lex-≤ = Core.Lex {A = A} ⊤ _≈_ _≺_

----------------------------------------------------------------------
-- Properties of Lex-<
----------------------------------------------------------------------

module _ {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} where
  private
    _≋_ = Pointwise _≈_
    _<_ = Lex-< _≈_ _≺_

  ¬[]<[] : ¬ [] < []
  ¬[]<[] (base ())

  module _ (≺-irrefl : Irreflexive _≈_ _≺_) where

    <-irrefl : ∀ {m n} → Irreflexive (_≋_ {m} {n}) (_<_ {m} {n})
    <-irrefl []            (base ())
    <-irrefl (x≈y ∷ xs≋ys) (this x≺y m≡n)   = ≺-irrefl x≈y x≺y
    <-irrefl (x≈y ∷ xs≋ys) (next _   xs<ys) = <-irrefl xs≋ys xs<ys

  module _ (≈-sym : Symmetric _≈_) (≺-resp-≈ : _≺_ Respects₂ _≈_) (≺-asym : Asymmetric _≺_) where

    <-asym : ∀ {n} → Asymmetric (_<_ {n} {n})
    <-asym (this x≺y m≡n) (this y≺x n≡m) = ≺-asym x≺y y≺x
    <-asym (this x≺y m≡n) (next y≈x ys<xs) = asym⇒irr ≺-resp-≈ ≈-sym ≺-asym (≈-sym y≈x) x≺y
    <-asym (next x≈y xs<ys) (this y≺x n≡m) = asym⇒irr ≺-resp-≈ ≈-sym ≺-asym (≈-sym x≈y) y≺x
    <-asym (next x≈y xs<ys) (next y≈x ys<xs) = <-asym xs<ys ys<xs

  <-antisym : Symmetric _≈_ → Irreflexive _≈_ _≺_ → Asymmetric _≺_ →
              ∀ {n} → Antisymmetric (_≋_ {n} {n}) _<_
  <-antisym = Core.antisym

  <-trans : IsPartialEquivalence _≈_ → _≺_ Respects₂ _≈_ → Transitive _≺_ →
            ∀ {m n o} → Trans (_<_ {m} {n}) (_<_ {n} {o}) _<_
  <-trans = Core.transitive

  module _ (≈-sym : Symmetric _≈_) (≺-cmp : Trichotomous _≈_ _≺_) where

    <-cmp : ∀ {n} → Trichotomous _≋_ (_<_ {n})
    <-cmp [] [] = tri≈ ¬[]<[] [] ¬[]<[]
    <-cmp (x ∷ xs) (y ∷ ys) with ≺-cmp x y
    ... | tri< x≺y x≉y x⊁y = tri< (this x≺y P.refl) (x≉y ∘ head) (≰-this (x≉y ∘ ≈-sym) x⊁y)
    ... | tri> x⊀y x≉y x≻y = tri> (≰-this x≉y x⊀y) (x≉y ∘ head) (this x≻y P.refl)
    ... | tri≈ x⊀y x≈y x⊁y with <-cmp xs ys
    ...   | tri< xs<ys xs≋̸ys xs≯ys = tri< (next x≈y xs<ys) (xs≋̸ys ∘ tail) (≰-next x⊁y xs≯ys)
    ...   | tri≈ xs≮ys xs≋ys xs≯ys = tri≈ (≰-next x⊀y xs≮ys) (x≈y ∷ xs≋ys) (≰-next x⊁y xs≯ys)
    ...   | tri> xs≮ys xs≋̸ys xs>ys = tri> (≰-next x⊀y xs≮ys) (xs≋̸ys ∘ tail) (next (≈-sym x≈y) xs>ys)

  <-decidable : Decidable _≈_ → Decidable _≺_ →
                ∀ {m n} → Decidable (_<_ {m} {n})
  <-decidable = Core.decidable (no id)

  <-respects₂ : IsPartialEquivalence _≈_ → _≺_ Respects₂ _≈_ →
                ∀ {n} → _Respects₂_ (_<_ {n} {n}) _≋_
  <-respects₂ = Core.respects₂

  <-irrelevant : Irrelevant _≈_ → Irrelevant _≺_ → Irreflexive _≈_ _≺_ →
                 ∀ {m n} → Irrelevant (_<_ {m} {n})
  <-irrelevant = Core.irrelevant (λ ())

----------------------------------------------------------------------
-- Structures

  <-isStrictPartialOrder : IsStrictPartialOrder _≈_ _≺_ →
                           ∀ {n} → IsStrictPartialOrder (_≋_ {n} {n}) _<_
  <-isStrictPartialOrder ≺-isStrictPartialOrder {n} = record
    { isEquivalence = Pointwise.isEquivalence O.isEquivalence n
    ; irrefl        = <-irrefl O.irrefl
    ; trans         = <-trans O.Eq.isPartialEquivalence O.<-resp-≈ O.trans
    ; <-resp-≈      = <-respects₂ O.Eq.isPartialEquivalence O.<-resp-≈
    } where module O = IsStrictPartialOrder ≺-isStrictPartialOrder

  <-isDecStrictPartialOrder : IsDecStrictPartialOrder _≈_ _≺_ →
                              ∀ {n} → IsDecStrictPartialOrder (_≋_ {n} {n}) _<_
  <-isDecStrictPartialOrder ≺-isDecStrictPartialOrder = record
    { isStrictPartialOrder = <-isStrictPartialOrder O.isStrictPartialOrder
    ; _≟_                  = Pointwise.decidable O._≟_
    ; _<?_                 = <-decidable O._≟_ O._<?_
    } where module O = IsDecStrictPartialOrder ≺-isDecStrictPartialOrder

  <-isStrictTotalOrder : IsStrictTotalOrder _≈_ _≺_ →
                         ∀ {n} → IsStrictTotalOrder (_≋_ {n} {n}) _<_
  <-isStrictTotalOrder ≺-isStrictTotalOrder {n} = record
    { isEquivalence = Pointwise.isEquivalence O.isEquivalence n
    ; trans         = <-trans O.Eq.isPartialEquivalence O.<-resp-≈ O.trans
    ; compare       = <-cmp O.Eq.sym O.compare
    } where module O = IsStrictTotalOrder ≺-isStrictTotalOrder

----------------------------------------------------------------------
-- Bundles for Lex-<

<-strictPartialOrder : StrictPartialOrder a ℓ₁ ℓ₂ → ℕ → StrictPartialOrder _ _ _
<-strictPartialOrder ≺-spo n = record
  { isStrictPartialOrder = <-isStrictPartialOrder isStrictPartialOrder {n = n}
  } where open StrictPartialOrder ≺-spo

<-decStrictPartialOrder : DecStrictPartialOrder a ℓ₁ ℓ₂ → ℕ → DecStrictPartialOrder _ _ _
<-decStrictPartialOrder ≺-dspo n = record
  { isDecStrictPartialOrder = <-isDecStrictPartialOrder isDecStrictPartialOrder {n = n}
  } where open DecStrictPartialOrder ≺-dspo

<-strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂ → ℕ → StrictTotalOrder _ _ _
<-strictTotalOrder ≺-sto n = record
  { isStrictTotalOrder = <-isStrictTotalOrder isStrictTotalOrder {n = n}
  } where open StrictTotalOrder ≺-sto

----------------------------------------------------------------------
-- Properties of Lex-≤
----------------------------------------------------------------------

module _ {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} where
  private
    _≋_ = Pointwise _≈_
    _<_ = Lex-< _≈_ _≺_
    _≤_ = Lex-≤ _≈_ _≺_

  <⇒≤ : ∀ {m n} {xs : Vec A m} {ys : Vec A n} → xs < ys → xs ≤ ys
  <⇒≤ = Core.map-P ⊥-elim

  ≤-refl : ∀ {m n} → (_≋_ {m} {n}) ⇒ _≤_
  ≤-refl []            = base tt
  ≤-refl (x≈y ∷ xs≋ys) = next x≈y (≤-refl xs≋ys)

  ≤-antisym : Symmetric _≈_ → Irreflexive _≈_ _≺_ → Asymmetric _≺_ →
              ∀ {n} → Antisymmetric (_≋_ {n} {n}) _≤_
  ≤-antisym = Core.antisym

  ≤-resp₂ : IsPartialEquivalence _≈_ → _≺_ Respects₂ _≈_ →
            ∀ {n} → _Respects₂_ (_≤_ {n} {n}) _≋_
  ≤-resp₂ = Core.respects₂

  ≤-trans : IsPartialEquivalence _≈_ → _≺_ Respects₂ _≈_ → Transitive _≺_ →
            ∀ {m n o} → Trans (_≤_ {m} {n}) (_≤_ {n} {o}) _≤_
  ≤-trans = Core.transitive

  <-transʳ : IsPartialEquivalence _≈_ → _≺_ Respects₂ _≈_ → Transitive _≺_ →
             ∀ {m n o} → Trans (_≤_ {m} {n}) (_<_ {n} {o}) _<_
  <-transʳ ≈-equiv ≺-resp-≈ ≺-trans xs≤ys ys<zs = Core.map-P proj₂
    (Core.transitive′ ≈-equiv ≺-resp-≈ ≺-trans xs≤ys ys<zs)

  <-transˡ : IsPartialEquivalence _≈_ → _≺_ Respects₂ _≈_ → Transitive _≺_ →
             ∀ {m n o} → Trans (_<_ {m} {n}) (_≤_ {n} {o}) _<_
  <-transˡ ≈-equiv ≺-resp-≈ ≺-trans xs<ys ys≤zs = Core.map-P proj₁
    (Core.transitive′ ≈-equiv ≺-resp-≈ ≺-trans xs<ys ys≤zs)

  -- Note that trichotomy is an unnecessarily strong precondition for
  -- the following lemma.

  module _ (≈-sym : Symmetric _≈_) (≺-cmp : Trichotomous _≈_ _≺_) where

    ≤-total : ∀ {n} → Total (_≤_ {n} {n})
    ≤-total [] [] = inj₁ (base tt)
    ≤-total (x ∷ xs) (y ∷ ys) with ≺-cmp x y
    ... | tri< x≺y _   _   = inj₁ (this x≺y P.refl)
    ... | tri> _   _   x≻y = inj₂ (this x≻y P.refl)
    ... | tri≈ _   x≈y _ with ≤-total xs ys
    ...   | inj₁ xs<ys = inj₁ (next x≈y xs<ys)
    ...   | inj₂ xs>ys = inj₂ (next (≈-sym x≈y) xs>ys)

  ≤-dec : Decidable _≈_ → Decidable _≺_ →
          ∀ {m n} → Decidable (_≤_ {m} {n})
  ≤-dec = Core.decidable (yes tt)

  ≤-irrelevant : Irrelevant _≈_ → Irrelevant _≺_ → Irreflexive _≈_ _≺_ →
                 ∀ {m n} → Irrelevant (_≤_ {m} {n})
  ≤-irrelevant = Core.irrelevant ⊤-irrelevant

----------------------------------------------------------------------
-- Structures

  ≤-isPreorder : IsEquivalence _≈_ → Transitive _≺_ → _≺_ Respects₂ _≈_ →
                 ∀ {n} → IsPreorder (_≋_ {n} {n}) _≤_
  ≤-isPreorder ≈-equiv ≺-trans ≺-resp-≈ {n} = record
    { isEquivalence = Pointwise.isEquivalence ≈-equiv n
    ; reflexive     = ≤-refl
    ; trans         = ≤-trans (IsEquivalence.isPartialEquivalence ≈-equiv) ≺-resp-≈ ≺-trans
    }

  ≤-isPartialOrder : IsStrictPartialOrder _≈_ _≺_ →
                     ∀ {n} → IsPartialOrder (_≋_ {n} {n}) _≤_
  ≤-isPartialOrder ≺-isStrictPartialOrder = record
    { isPreorder = ≤-isPreorder isEquivalence trans <-resp-≈
    ; antisym    = ≤-antisym Eq.sym irrefl asym
    } where open IsStrictPartialOrder ≺-isStrictPartialOrder

  ≤-isDecPartialOrder : IsDecStrictPartialOrder _≈_ _≺_ →
                        ∀ {n} → IsDecPartialOrder (_≋_ {n} {n}) _≤_
  ≤-isDecPartialOrder ≺-isDecStrictPartialOrder = record
    { isPartialOrder = ≤-isPartialOrder isStrictPartialOrder
    ; _≟_            = Pointwise.decidable _≟_
    ; _≤?_           = ≤-dec _≟_ _<?_
    } where open IsDecStrictPartialOrder ≺-isDecStrictPartialOrder

  ≤-isTotalOrder : IsStrictTotalOrder _≈_ _≺_ →
                   ∀ {n} → IsTotalOrder (_≋_ {n} {n}) _≤_
  ≤-isTotalOrder ≺-isStrictTotalOrder = record
    { isPartialOrder = ≤-isPartialOrder isStrictPartialOrder
    ; total          = ≤-total Eq.sym compare
    } where open IsStrictTotalOrder ≺-isStrictTotalOrder

  ≤-isDecTotalOrder : IsStrictTotalOrder _≈_ _≺_ →
                      ∀ {n} → IsDecTotalOrder (_≋_ {n} {n}) _≤_
  ≤-isDecTotalOrder ≺-isStrictTotalOrder = record
    { isTotalOrder = ≤-isTotalOrder ≺-isStrictTotalOrder
    ; _≟_          = Pointwise.decidable _≟_
    ; _≤?_         = ≤-dec _≟_ _<?_
    } where open IsStrictTotalOrder ≺-isStrictTotalOrder

----------------------------------------------------------------------
-- Bundles

≤-preorder : Preorder a ℓ₁ ℓ₂ → ℕ → Preorder _ _ _
≤-preorder ≺-pre n = record
  { isPreorder = ≤-isPreorder isEquivalence trans ∼-resp-≈ {n = n}
  } where open Preorder ≺-pre

≤-partialOrder : StrictPartialOrder a ℓ₁ ℓ₂ → ℕ → Poset _ _ _
≤-partialOrder ≺-spo n = record
  { isPartialOrder = ≤-isPartialOrder isStrictPartialOrder {n = n}
  } where open StrictPartialOrder ≺-spo

≤-decPartialOrder : DecStrictPartialOrder a ℓ₁ ℓ₂ → ℕ → DecPoset _ _ _
≤-decPartialOrder ≺-spo n = record
  { isDecPartialOrder = ≤-isDecPartialOrder isDecStrictPartialOrder {n = n}
  } where open DecStrictPartialOrder ≺-spo

≤-totalOrder : StrictTotalOrder a ℓ₁ ℓ₂ → ℕ → TotalOrder _ _ _
≤-totalOrder ≺-sto n = record
  { isTotalOrder = ≤-isTotalOrder isStrictTotalOrder {n = n}
  } where open StrictTotalOrder ≺-sto

≤-decTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂ → ℕ → DecTotalOrder _ _ _
≤-decTotalOrder ≺-sto n = record
  { isDecTotalOrder = ≤-isDecTotalOrder isStrictTotalOrder {n = n}
  } where open StrictTotalOrder ≺-sto

----------------------------------------------------------------------
-- Equational Reasoning
----------------------------------------------------------------------

module ≤-Reasoning {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂}
                   (≈-isEquivalence : IsEquivalence _≈_)
                   (≺-trans : Transitive _≺_)
                   (≺-resp-≈ : _≺_ Respects₂ _≈_)
                   (n : ℕ)
                   where

  private
    ≈-isPartialEquivalence = IsEquivalence.isPartialEquivalence ≈-isEquivalence

  open import Relation.Binary.Reasoning.Base.Triple
    (≤-isPreorder ≈-isEquivalence ≺-trans ≺-resp-≈)
    (<-trans ≈-isPartialEquivalence ≺-resp-≈ ≺-trans)
    (<-respects₂ ≈-isPartialEquivalence ≺-resp-≈)
    (<⇒≤ {m = n})
    (<-transˡ ≈-isPartialEquivalence ≺-resp-≈ ≺-trans)
    (<-transʳ ≈-isPartialEquivalence ≺-resp-≈ ≺-trans)
    public
