------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of lists
------------------------------------------------------------------------

-- The definitions of lexicographic ordering used here are suitable if
-- the argument order is a strict partial order.

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Relation.Binary.Lex.Strict where

open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as Pointwise using (Pointwise; []; _∷_; head; tail)
open import Function using (id; _∘_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary
open import Relation.Binary.Consequences
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Level using (_⊔_)

open import Data.Vec.Relation.Binary.Lex.Core as Core public
  using (base; this; next; ¬≤-this; ¬≤-next)

----------------------------------------------------------------------
-- Strict lexicographic ordering.

module _ {a ℓ₁ ℓ₂} {A : Set a} where

  Lex-< : (_≈_ : Rel A ℓ₁) (_≺_ : Rel A ℓ₂) → ∀ {m n} → REL (Vec A m) (Vec A n) (a ⊔ ℓ₁ ⊔ ℓ₂)
  Lex-< = Core.Lex ⊥

  module _ {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} where
    private
      _≋_ = Pointwise _≈_
      _<_ = Lex-< _≈_ _≺_

    ¬[]Lex-<[] : ¬ [] < []
    ¬[]Lex-<[] (base ())

    module _ (≺-irrefl : Irreflexive _≈_ _≺_) where
      Lex-<-irrefl : ∀ {m n} → Irreflexive (_≋_ {m} {n}) (_<_ {m} {n})
      Lex-<-irrefl []            (base ())
      Lex-<-irrefl (x≈y ∷ xs≋ys) (this x≺y m≡n)   = ≺-irrefl x≈y x≺y
      Lex-<-irrefl (x≈y ∷ xs≋ys) (next _   xs<ys) = Lex-<-irrefl xs≋ys xs<ys

    module _ (≈-sym : Symmetric _≈_) (≺-resp-≈ : _≺_ Respects₂ _≈_) (≺-asym : Asymmetric _≺_) where
      Lex-<-asym : ∀ {n} → Asymmetric (_<_ {n} {n})
      Lex-<-asym (this x≺y m≡n) (this y≺x n≡m) = ≺-asym x≺y y≺x
      Lex-<-asym (this x≺y m≡n) (next y≈x ys<xs) = asym⟶irr ≺-resp-≈ ≈-sym ≺-asym (≈-sym y≈x) x≺y
      Lex-<-asym (next x≈y xs<ys) (this y≺x n≡m) = asym⟶irr ≺-resp-≈ ≈-sym ≺-asym (≈-sym x≈y) y≺x
      Lex-<-asym (next x≈y xs<ys) (next y≈x ys<xs) = Lex-<-asym xs<ys ys<xs

    Lex-<-antisym : ∀ {n} → Symmetric _≈_ → Irreflexive _≈_ _≺_ → Asymmetric _≺_ → Antisymmetric (_≋_ {n} {n}) _<_
    Lex-<-antisym ≈-sym ≺-irrefl ≺-asym = Core.Lex-antisym ≈-sym ≺-irrefl ≺-asym

    Lex-<-trans : ∀ {m n o} → IsPartialEquivalence _≈_ → _≺_ Respects₂ _≈_ → Transitive _≺_ → Trans (_<_ {m} {n}) (_<_ {n} {o}) _<_
    Lex-<-trans ≈-eqiv ≺-resp-≈ ≺-trans = Core.Lex-trans ≈-eqiv ≺-resp-≈ ≺-trans

    module _ (≈-sym : Symmetric _≈_) (≺-cmp : Trichotomous _≈_ _≺_) where
      Lex-<-cmp : ∀ {n} → Trichotomous _≋_ (_<_ {n})
      Lex-<-cmp [] [] = tri≈ ¬[]Lex-<[] [] ¬[]Lex-<[]
      Lex-<-cmp (x ∷ xs) (y ∷ ys) with ≺-cmp x y
      ... | tri< x≺y x≉y x⊁y = tri< (this x≺y P.refl) (x≉y ∘ head) (¬≤-this (x≉y ∘ ≈-sym) x⊁y)
      ... | tri> x⊀y x≉y x≻y = tri> (¬≤-this x≉y x⊀y) (x≉y ∘ head) (this x≻y P.refl)
      ... | tri≈ x⊀y x≈y x⊁y with Lex-<-cmp xs ys
      ...   | tri< xs<ys xs≋̸ys xs≯ys = tri< (next x≈y xs<ys) (xs≋̸ys ∘ tail) (¬≤-next x⊁y xs≯ys)
      ...   | tri≈ xs≮ys xs≋ys xs≯ys = tri≈ (¬≤-next x⊀y xs≮ys) (x≈y ∷ xs≋ys) (¬≤-next x⊁y xs≯ys)
      ...   | tri> xs≮ys xs≋̸ys xs>ys = tri> (¬≤-next x⊀y xs≮ys) (xs≋̸ys ∘ tail) (next (≈-sym x≈y) xs>ys)

    Lex-<? : ∀ {m n} → Decidable _≈_ → Decidable _≺_ → Decidable (_<_ {m} {n})
    Lex-<? _≈?_ _≺?_ = Core.Lex? (no id) _≈?_ _≺?_

    Lex-<-respects₂ : ∀ {n} → IsPartialEquivalence _≈_ → _≺_ Respects₂ _≈_ → _Respects₂_ (_<_ {n} {n}) _≋_
    Lex-<-respects₂ ≈-equiv ≺-resp = Core.Lex-respects₂ ≈-equiv ≺-resp

    Lex-<-irrelevant : ∀ {m n} → Irreflexive _≈_ _≺_ → Irrelevant _≈_ → Irrelevant _≺_ → Irrelevant (_<_ {m} {n})
    Lex-<-irrelevant ≺-irrefl ≈-irrelevant ≺-irrelevant = Core.Lex-irrelevant ≺-irrefl (λ ()) ≈-irrelevant ≺-irrelevant

    Lex-<-isStrictPartialOrder : ∀ {n} → IsStrictPartialOrder _≈_ _≺_ → IsStrictPartialOrder (_≋_ {n} {n}) _<_
    Lex-<-isStrictPartialOrder {n} ≺-isStrictPartialOrder = record
      { isEquivalence = Pointwise.isEquivalence isEquivalence n
      ; irrefl = Lex-<-irrefl irrefl
      ; trans = Lex-<-trans (IsEquivalence.isPartialEquivalence isEquivalence) <-resp-≈ trans
      ; <-resp-≈ = Lex-<-respects₂ (IsEquivalence.isPartialEquivalence isEquivalence) <-resp-≈
      } where open IsStrictPartialOrder ≺-isStrictPartialOrder

    Lex-<-isDecStrictPartialOrder : ∀ {n} → IsDecStrictPartialOrder _≈_ _≺_ → IsDecStrictPartialOrder (_≋_ {n} {n}) _<_
    Lex-<-isDecStrictPartialOrder {n} ≺-isDecStrictPartialOrder = record
      { isStrictPartialOrder = Lex-<-isStrictPartialOrder isStrictPartialOrder
      ; _≟_ = Pointwise.decidable _≟_
      ; _<?_ = Lex-<? _≟_ _<?_
      } where open IsDecStrictPartialOrder ≺-isDecStrictPartialOrder

    Lex-<-isStrictTotalOrder : ∀ {n} → IsStrictTotalOrder _≈_ _≺_ → IsStrictTotalOrder (_≋_ {n} {n}) _<_
    Lex-<-isStrictTotalOrder {n} ≺-isStrictTotalOrder = record
      { isEquivalence = Pointwise.isEquivalence isEquivalence n
      ; trans = Lex-<-trans (IsEquivalence.isPartialEquivalence isEquivalence) <-resp-≈ trans
      ; compare = Lex-<-cmp (IsEquivalence.sym isEquivalence) compare
      } where open IsStrictTotalOrder ≺-isStrictTotalOrder

Lex-<-strictPartialOrder : ∀ {a ℓ₁ ℓ₂} → StrictPartialOrder a ℓ₁ ℓ₂ → ℕ → StrictPartialOrder _ _ _
Lex-<-strictPartialOrder ≺-spo n = record
  { isStrictPartialOrder = Lex-<-isStrictPartialOrder {n = n} isStrictPartialOrder
  } where open StrictPartialOrder ≺-spo

Lex-<-decStrictPartialOrder : ∀ {a ℓ₁ ℓ₂} → DecStrictPartialOrder a ℓ₁ ℓ₂ → ℕ → DecStrictPartialOrder _ _ _
Lex-<-decStrictPartialOrder ≺-dspo n = record
  { isDecStrictPartialOrder = Lex-<-isDecStrictPartialOrder {n = n} isDecStrictPartialOrder
  } where open DecStrictPartialOrder ≺-dspo

Lex-<-strictTotalOrder : ∀ {a ℓ₁ ℓ₂} → StrictTotalOrder a ℓ₁ ℓ₂ → ℕ → StrictTotalOrder _ _ _
Lex-<-strictTotalOrder ≺-sto n = record
  { isStrictTotalOrder = Lex-<-isStrictTotalOrder {n = n} isStrictTotalOrder
  } where open StrictTotalOrder ≺-sto

----------------------------------------------------------------------
-- Non-strict lexicographic ordering.

module _ {a ℓ₁ ℓ₂} {A : Set a} where

  Lex-≤ : (_≈_ : Rel A ℓ₁) (_≺_ : Rel A ℓ₂) → ∀ {m n} → REL (Vec A m) (Vec A n) (a ⊔ ℓ₁ ⊔ ℓ₂)
  Lex-≤ = Core.Lex ⊤

  -- Properties

  module _ {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} where
    private
      _≋_ = Pointwise _≈_
      _<_ = Lex-< _≈_ _≺_
      _≤_ = Lex-≤ _≈_ _≺_

    Lex-≤-refl : ∀ {m n} → (_≋_ {m} {n}) ⇒ _≤_
    Lex-≤-refl [] = base tt
    Lex-≤-refl (x≈y ∷ xs≋ys) = next x≈y (Lex-≤-refl xs≋ys)

    Lex-≤-antisym : ∀ {n} → Symmetric _≈_ → Irreflexive _≈_ _≺_ → Asymmetric _≺_ → Antisymmetric (_≋_ {n} {n}) _≤_
    Lex-≤-antisym ≈-sym ≺-irrefl ≺-asym = Core.Lex-antisym ≈-sym ≺-irrefl ≺-asym

    Lex-≤-trans : ∀ {m n o} → IsPartialEquivalence _≈_ → _≺_ Respects₂ _≈_ → Transitive _≺_ → Trans (_≤_ {m} {n}) (_≤_ {n} {o}) _≤_
    Lex-≤-trans ≈-equiv ≺-resp-≈ ≺-trans = Core.Lex-trans ≈-equiv ≺-resp-≈ ≺-trans

    Lex-<-transʳ : ∀ {m n o} → IsPartialEquivalence _≈_ → _≺_ Respects₂ _≈_ → Transitive _≺_ → Trans (_≤_ {m} {n}) (_<_ {n} {o}) _<_
    Lex-<-transʳ ≈-equiv ≺-resp-≈ ≺-trans xs≤ys ys<zs = Core.Lex-mapP proj₂ (Core.Lex-trans′ ≈-equiv ≺-resp-≈ ≺-trans xs≤ys ys<zs)

    Lex-<-transˡ : ∀ {m n o} → IsPartialEquivalence _≈_ → _≺_ Respects₂ _≈_ → Transitive _≺_ → Trans (_<_ {m} {n}) (_≤_ {n} {o}) _<_
    Lex-<-transˡ ≈-equiv ≺-resp-≈ ≺-trans xs<ys ys≤zs = Core.Lex-mapP proj₁ (Core.Lex-trans′ ≈-equiv ≺-resp-≈ ≺-trans xs<ys ys≤zs)

    -- Note that trichotomy is an unnecessarily strong precondition for
    -- the following lemma.

    module _ (≈-sym : Symmetric _≈_) (≺-cmp : Trichotomous _≈_ _≺_) where
      Lex-≤-total : ∀ {n} → Total (_≤_ {n} {n})
      Lex-≤-total [] [] = inj₁ (base tt)
      Lex-≤-total (x ∷ xs) (y ∷ ys) with ≺-cmp x y
      ... | tri< x≺y _   _   = inj₁ (this x≺y P.refl)
      ... | tri> _   _   x≻y = inj₂ (this x≻y P.refl)
      ... | tri≈ _   x≈y _ with Lex-≤-total xs ys
      ...   | inj₁ xs<ys = inj₁ (next x≈y xs<ys)
      ...   | inj₂ xs>ys = inj₂ (next (≈-sym x≈y) xs>ys)

    Lex-≤? : ∀ {m n} → Decidable _≈_ → Decidable _≺_ → Decidable (_≤_ {m} {n})
    Lex-≤? _≈?_ _≺?_ = Core.Lex? (yes tt) _≈?_ _≺?_

    Lex-≤-respects₂ : ∀ {n} → IsPartialEquivalence _≈_ → _≺_ Respects₂ _≈_ → _Respects₂_ (_≤_ {n} {n}) _≋_
    Lex-≤-respects₂ ≈-equiv ≺-resp = Core.Lex-respects₂ ≈-equiv ≺-resp

    Lex-≤-irrelevant : ∀ {m n} → Irreflexive _≈_ _≺_ → Irrelevant _≈_ → Irrelevant _≺_ → Irrelevant (_≤_ {m} {n})
    Lex-≤-irrelevant ≺-irrefl ≈-irrelevant ≺-irrelevant = Core.Lex-irrelevant ≺-irrefl (λ {tt tt → P.refl}) ≈-irrelevant ≺-irrelevant

    Lex-≤-isPreorder : ∀ {n} → IsEquivalence _≈_ → Transitive _≺_ → _≺_ Respects₂ _≈_ → IsPreorder (_≋_ {n} {n}) _≤_
    Lex-≤-isPreorder {n} ≈-equiv ≺-trans ≺-resp-≈ = record
      { isEquivalence = Pointwise.isEquivalence ≈-equiv n
      ; reflexive = Lex-≤-refl
      ; trans = Lex-≤-trans (IsEquivalence.isPartialEquivalence ≈-equiv) ≺-resp-≈ ≺-trans
      }

    Lex-≤-isPartialOrder : ∀ {n} → IsStrictPartialOrder _≈_ _≺_ → IsPartialOrder (_≋_ {n} {n}) _≤_
    Lex-≤-isPartialOrder {n} ≺-isStrictPartialOrder = record
      { isPreorder = Lex-≤-isPreorder isEquivalence trans <-resp-≈
      ; antisym = Lex-≤-antisym Eq.sym irrefl asym
      } where open IsStrictPartialOrder ≺-isStrictPartialOrder

    Lex-≤-isDecPartialOrder : ∀ {n} → IsDecStrictPartialOrder _≈_ _≺_ → IsDecPartialOrder (_≋_ {n} {n}) _≤_
    Lex-≤-isDecPartialOrder {n} ≺-isDecStrictPartialOrder = record
      { isPartialOrder = Lex-≤-isPartialOrder isStrictPartialOrder
      ; _≟_ = Pointwise.decidable _≟_
      ; _≤?_ = Lex-≤? _≟_ _<?_
      } where open IsDecStrictPartialOrder ≺-isDecStrictPartialOrder

    Lex-≤-isTotalOrder : ∀ {n} → IsStrictTotalOrder _≈_ _≺_ → IsTotalOrder (_≋_ {n} {n}) _≤_
    Lex-≤-isTotalOrder {n} ≺-isStrictTotalOrder = record
      { isPartialOrder = Lex-≤-isPartialOrder isStrictPartialOrder
      ; total = Lex-≤-total Eq.sym compare
      } where open IsStrictTotalOrder ≺-isStrictTotalOrder

    Lex-≤-isDecTotalOrder : ∀ {n} → IsStrictTotalOrder _≈_ _≺_ → IsDecTotalOrder (_≋_ {n} {n}) _≤_
    Lex-≤-isDecTotalOrder {n} ≺-isStrictTotalOrder = record
      { isTotalOrder = Lex-≤-isTotalOrder ≺-isStrictTotalOrder
      ; _≟_ = Pointwise.decidable _≟_
      ; _≤?_ = Lex-≤? _≟_ _<?_
      } where open IsStrictTotalOrder ≺-isStrictTotalOrder

    Lex-<⇒Lex-≤ : ∀ {m n} {xs : Vec A m} {ys : Vec A n} → xs < ys → xs ≤ ys
    Lex-<⇒Lex-≤ = Core.Lex-mapP ⊥-elim

    module ≤-Reasoning (≈-equiv : IsEquivalence _≈_) (≺-trans : Transitive _≺_) (≺-resp-≈ : _≺_ Respects₂ _≈_) (n : ℕ) where
      open import Relation.Binary.Reasoning.Base.Triple
        (Lex-≤-isPreorder {n} ≈-equiv ≺-trans ≺-resp-≈)
        (Lex-<-trans {m = n} {n = n} {o = n} (IsEquivalence.isPartialEquivalence ≈-equiv) ≺-resp-≈ ≺-trans)
        (Lex-<-respects₂ (IsEquivalence.isPartialEquivalence ≈-equiv) ≺-resp-≈)
        (Lex-<⇒Lex-≤ {n} {n})
        (Lex-<-transˡ (IsEquivalence.isPartialEquivalence ≈-equiv) ≺-resp-≈ ≺-trans)
        (Lex-<-transʳ (IsEquivalence.isPartialEquivalence ≈-equiv) ≺-resp-≈ ≺-trans)
        public


Lex-≤-preorder : ∀ {a ℓ₁ ℓ₂} → Preorder a ℓ₁ ℓ₂ → ℕ → Preorder _ _ _
Lex-≤-preorder ≺-pre n = record
  { isPreorder = Lex-≤-isPreorder {n = n} isEquivalence trans ∼-resp-≈
  } where open Preorder ≺-pre

Lex-≤-partialOrder : ∀ {a ℓ₁ ℓ₂} → StrictPartialOrder a ℓ₁ ℓ₂ → ℕ → Poset _ _ _
Lex-≤-partialOrder ≺-spo n = record
  { isPartialOrder = Lex-≤-isPartialOrder {n = n} isStrictPartialOrder
  } where open StrictPartialOrder ≺-spo

Lex-≤-decPartialOrder : ∀ {a ℓ₁ ℓ₂} → DecStrictPartialOrder a ℓ₁ ℓ₂ → ℕ → DecPoset _ _ _
Lex-≤-decPartialOrder ≺-spo n = record
  { isDecPartialOrder = Lex-≤-isDecPartialOrder {n = n} isDecStrictPartialOrder
  } where open DecStrictPartialOrder ≺-spo

Lex-≤-totalOrder : ∀ {a ℓ₁ ℓ₂} → StrictTotalOrder a ℓ₁ ℓ₂ → ℕ → TotalOrder _ _ _
Lex-≤-totalOrder ≺-sto n = record
  { isTotalOrder = Lex-≤-isTotalOrder {n = n} isStrictTotalOrder
  } where open StrictTotalOrder ≺-sto

Lex-≤-decTotalOrder : ∀ {a ℓ₁ ℓ₂} → StrictTotalOrder a ℓ₁ ℓ₂ → ℕ → DecTotalOrder _ _ _
Lex-≤-decTotalOrder ≺-sto n = record
  { isDecTotalOrder = Lex-≤-isDecTotalOrder {n = n} isStrictTotalOrder
  } where open StrictTotalOrder ≺-sto

