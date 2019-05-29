------------------------------------------------------------------------
-- The Agda standard library
--
-- Heterogeneous equality
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Relation.Binary.HeterogeneousEquality where

import Axiom.Extensionality.Heterogeneous as Ext
open import Data.Product
open import Data.Unit.NonEta
open import Function.Core
open import Function.Inverse using (Inverse)
open import Level
open import Relation.Nullary
open import Relation.Unary using (Pred)
open import Relation.Binary
open import Relation.Binary.Consequences
open import Relation.Binary.Indexed.Heterogeneous
  using (IndexedSetoid)
open import Relation.Binary.Indexed.Heterogeneous.Construct.At
  using (_atₛ_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

import Relation.Binary.HeterogeneousEquality.Core as Core

private
  variable
    a b c p ℓ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Heterogeneous equality

infix 4 _≇_

open Core public using (_≅_; refl)

-- Nonequality.

_≇_ : ∀ {A : Set a} → A → {B : Set b} → B → Set a
x ≇ y = ¬ x ≅ y

------------------------------------------------------------------------
-- Conversion

open Core public using (≅-to-≡; ≡-to-≅)

≅-to-type-≡ : ∀ {A B : Set a} {x : A} {y : B} → x ≅ y → A ≡ B
≅-to-type-≡ refl = refl

≅-to-subst-≡ : ∀ {A B : Set a} {x : A} {y : B} → (p : x ≅ y) →
               P.subst (λ x → x) (≅-to-type-≡ p) x ≡ y
≅-to-subst-≡ refl = refl

------------------------------------------------------------------------
-- Some properties

reflexive : _⇒_ {A = A} _≡_ (λ x y → x ≅ y)
reflexive refl = refl

sym : ∀ {x : A} {y : B} → x ≅ y → y ≅ x
sym refl = refl

trans : ∀ {x : A} {y : B} {z : C} → x ≅ y → y ≅ z → x ≅ z
trans refl eq = eq

subst : Substitutive {A = A} (λ x y → x ≅ y) ℓ
subst P refl p = p

subst₂ : ∀ (_∼_ : REL A B ℓ) {x y u v} → x ≅ y → u ≅ v → x ∼ u → y ∼ v
subst₂ _ refl refl p = p

subst-removable : ∀ (P : Pred A p) {x y} (eq : x ≅ y) z →
                  subst P eq z ≅ z
subst-removable P refl z = refl

≡-subst-removable : ∀ (P : Pred A p) {x y} (eq : x ≡ y) z →
                    P.subst P eq z ≅ z
≡-subst-removable P refl z = refl

cong : ∀ {A : Set a} {B : A → Set b} {x y}
       (f : (x : A) → B x) → x ≅ y → f x ≅ f y
cong f refl = refl

cong-app : ∀ {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
           f ≅ g → (x : A) → f x ≅ g x
cong-app refl x = refl

cong₂ : ∀ {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {x y u v}
        (f : (x : A) (y : B x) → C x y) → x ≅ y → u ≅ v → f x u ≅ f y v
cong₂ f refl refl = refl

resp₂ : ∀ (∼ : Rel A ℓ) → ∼ Respects₂ (λ x y → x ≅ y)
resp₂ _∼_ = subst⟶resp₂ _∼_ subst

module _ {I : Set ℓ} (A : I → Set a) {B : {k : I} → A k → Set b} where

  icong : {i j : I} {x : A i} {y : A j} →
          i ≡ j →
          (f : {k : I} → (z : A k) → B z) →
          x ≅ y →
          f x ≅ f y
  icong refl _ refl = refl

  icong₂ : {C : {k : I} → (a : A k) → B a → Set c}
           {i j : I} {x : A i} {y : A j} {u : B x} {v : B y} →
           i ≡ j →
           (f : {k : I} → (z : A k) → (w : B z) → C z w) →
           x ≅ y → u ≅ v →
           f x u ≅ f y v
  icong₂ refl _ refl refl = refl

  icong-subst-removable : {i j : I} (eq : i ≅ j)
                          (f : {k : I} → (z : A k) → B z)
                          (x : A i) →
                          f (subst A eq x) ≅ f x
  icong-subst-removable refl _ _ = refl

  icong-≡-subst-removable : {i j : I} (eq : i ≡ j)
                            (f : {k : I} → (z : A k) → B z)
                            (x : A i) →
                            f (P.subst A eq x) ≅ f x
  icong-≡-subst-removable refl _ _ = refl

------------------------------------------------------------------------
--Proof irrelevance

≅-irrelevant : {A B : Set ℓ} → Irrelevant ((A → B → Set ℓ) ∋ λ a → a ≅_)
≅-irrelevant refl refl = refl

module _ {A C : Set a} {B D : Set ℓ}
         {w : A} {x : B} {y : C} {z : D} where

 ≅-heterogeneous-irrelevant : (p : w ≅ x) (q : y ≅ z) → x ≅ y → p ≅ q
 ≅-heterogeneous-irrelevant refl refl refl = refl

 ≅-heterogeneous-irrelevantˡ : (p : w ≅ x) (q : y ≅ z) → w ≅ y → p ≅ q
 ≅-heterogeneous-irrelevantˡ refl refl refl = refl

 ≅-heterogeneous-irrelevantʳ : (p : w ≅ x) (q : y ≅ z) → x ≅ z → p ≅ q
 ≅-heterogeneous-irrelevantʳ refl refl refl = refl

------------------------------------------------------------------------
-- Structures

isEquivalence : IsEquivalence {A = A} (λ x y → x ≅ y)
isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

setoid : Set ℓ → Setoid ℓ ℓ
setoid A = record
  { Carrier       = A
  ; _≈_           = λ x y → x ≅ y
  ; isEquivalence = isEquivalence
  }

indexedSetoid : (A → Set b) → IndexedSetoid A _ _
indexedSetoid B = record
  { Carrier       = B
  ; _≈_           = λ x y → x ≅ y
  ; isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  }

≡↔≅ : ∀ {A : Set a} (B : A → Set b) {x : A} →
      Inverse (P.setoid (B x)) ((indexedSetoid B) atₛ x)
≡↔≅ B = record
  { to         = record { _⟨$⟩_ = id; cong = ≡-to-≅ }
  ; from       = record { _⟨$⟩_ = id; cong = ≅-to-≡ }
  ; inverse-of = record
    { left-inverse-of  = λ _ → refl
    ; right-inverse-of = λ _ → refl
    }
  }

decSetoid : Decidable {A = A} {B = A} (λ x y → x ≅ y) →
            DecSetoid _ _
decSetoid dec = record
  { _≈_              = λ x y → x ≅ y
  ; isDecEquivalence = record
      { isEquivalence = isEquivalence
      ; _≟_           = dec
      }
  }

isPreorder : IsPreorder {A = A} (λ x y → x ≅ y) (λ x y → x ≅ y)
isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = id
  ; trans         = trans
  }

isPreorder-≡ : IsPreorder {A = A} _≡_ (λ x y → x ≅ y)
isPreorder-≡ = record
  { isEquivalence = P.isEquivalence
  ; reflexive     = reflexive
  ; trans         = trans
  }

preorder : Set ℓ → Preorder ℓ ℓ ℓ
preorder A = record
  { Carrier    = A
  ; _≈_        = _≡_
  ; _∼_        = λ x y → x ≅ y
  ; isPreorder = isPreorder-≡
  }

------------------------------------------------------------------------
-- Convenient syntax for equational reasoning

module ≅-Reasoning where

  -- The code in `Relation.Binary.Reasoning.Setoid` cannot handle
  -- heterogeneous equalities, hence the code duplication here.

  infix  4 _IsRelatedTo_
  infix  3 _∎
  infixr 2 _≅⟨_⟩_ _≅˘⟨_⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_ _≡⟨⟩_
  infix  1 begin_

  data _IsRelatedTo_ {A : Set ℓ} (x : A) {B : Set ℓ} (y : B) :
                     Set ℓ where
    relTo : (x≅y : x ≅ y) → x IsRelatedTo y

  begin_ : ∀ {x : A} {y : B} → x IsRelatedTo y → x ≅ y
  begin relTo x≅y = x≅y

  _≅⟨_⟩_ : ∀ (x : A) {y : B} {z : C} →
           x ≅ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≅⟨ x≅y ⟩ relTo y≅z = relTo (trans x≅y y≅z)

  _≅˘⟨_⟩_ : ∀ (x : A) {y : B} {z : C} →
            y ≅ x → y IsRelatedTo z → x IsRelatedTo z
  _ ≅˘⟨ y≅x ⟩ relTo y≅z = relTo (trans (sym y≅x) y≅z)

  _≡⟨_⟩_ : ∀ (x : A) {y : A} {z : C} →
           x ≡ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≡⟨ x≡y ⟩ relTo y≅z = relTo (trans (reflexive x≡y) y≅z)

  _≡˘⟨_⟩_ : ∀ (x : A) {y : A} {z : C} →
            y ≡ x → y IsRelatedTo z → x IsRelatedTo z
  _ ≡˘⟨ y≡x ⟩ relTo y≅z = relTo (trans (sym (reflexive y≡x)) y≅z)

  _≡⟨⟩_ : ∀ (x : A) {y : B} → x IsRelatedTo y → x IsRelatedTo y
  _ ≡⟨⟩ x≅y = x≅y

  _∎ : ∀ (x : A) → x IsRelatedTo x
  _∎ _ = relTo refl

------------------------------------------------------------------------
-- Inspect

-- Inspect can be used when you want to pattern match on the result r
-- of some expression e, and you also need to "remember" that r ≡ e.

record Reveal_·_is_ {A : Set a} {B : A → Set b}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set (a ⊔ b) where
  constructor [_]
  field eq : f x ≅ y

inspect : ∀ {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = [ refl ]

-- Example usage:

-- f x y with g x | inspect g x
-- f x y | c z | [ eq ] = ...


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.15

proof-irrelevance = ≅-irrelevant
{-# WARNING_ON_USAGE proof-irrelevance
"Warning: proof-irrelevance was deprecated in v0.15.
Please use ≅-irrelevant instead."
#-}

-- Version 1.0

≅-irrelevance = ≅-irrelevant
{-# WARNING_ON_USAGE ≅-irrelevance
"Warning: ≅-irrelevance was deprecated in v1.0.
Please use ≅-irrelevant instead."
#-}
≅-heterogeneous-irrelevance = ≅-heterogeneous-irrelevant
{-# WARNING_ON_USAGE ≅-heterogeneous-irrelevance
"Warning: ≅-heterogeneous-irrelevance was deprecated in v1.0.
Please use ≅-heterogeneous-irrelevant instead."
#-}
≅-heterogeneous-irrelevanceˡ = ≅-heterogeneous-irrelevantˡ
{-# WARNING_ON_USAGE ≅-heterogeneous-irrelevanceˡ
"Warning: ≅-heterogeneous-irrelevanceˡ was deprecated in v1.0.
Please use ≅-heterogeneous-irrelevantˡ instead."
#-}
≅-heterogeneous-irrelevanceʳ = ≅-heterogeneous-irrelevantʳ
{-# WARNING_ON_USAGE ≅-heterogeneous-irrelevanceʳ
"Warning: ≅-heterogeneous-irrelevanceʳ was deprecated in v1.0.
Please use ≅-heterogeneous-irrelevantʳ instead."
#-}
Extensionality = Ext.Extensionality
{-# WARNING_ON_USAGE Extensionality
"Warning: Extensionality was deprecated in v1.0.
Please use Extensionality from `Axiom.Extensionality.Heterogeneous` instead."
#-}
≡-ext-to-≅-ext = Ext.≡-ext⇒≅-ext
{-# WARNING_ON_USAGE ≡-ext-to-≅-ext
"Warning: ≡-ext-to-≅-ext was deprecated in v1.0.
Please use ≡-ext⇒≅-ext from `Axiom.Extensionality.Heterogeneous` instead."
#-}
