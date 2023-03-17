------------------------------------------------------------------------
-- The Agda standard library
--
-- Maybe-related properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Maybe.Properties where

open import Algebra.Bundles
import Algebra.Structures as Structures
import Algebra.Definitions as Definitions
open import Data.Maybe.Base
open import Data.Maybe.Relation.Unary.All using (All; just; nothing)
open import Data.Product using (_,_)
open import Function
open import Level using (Level)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Decidable using (map′)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Equality

just-injective : ∀ {x y} → (Maybe A ∋ just x) ≡ just y → x ≡ y
just-injective refl = refl

≡-dec : Decidable _≡_ → Decidable {A = Maybe A} _≡_
≡-dec _≟_ nothing  nothing  = yes refl
≡-dec _≟_ (just x) nothing  = no λ()
≡-dec _≟_ nothing  (just y) = no λ()
≡-dec _≟_ (just x) (just y) = map′ (cong just) just-injective (x ≟ y)

------------------------------------------------------------------------
-- map

map-id : map id ≗ id {A = Maybe A}
map-id (just x) = refl
map-id nothing  = refl

map-id-local : ∀ {f : A → A} {mx} → All (λ x → f x ≡ x) mx → map f mx ≡ mx
map-id-local (just eq) = cong just eq
map-id-local nothing   = refl

map-<∣> : ∀ (f : A → B) mx my →
  map f (mx <∣> my) ≡ map f mx <∣> map f my
map-<∣> f (just x) my = refl
map-<∣> f nothing  my = refl

map-cong : {f g : A → B} → f ≗ g → map f ≗ map g
map-cong f≗g (just x) = cong just (f≗g x)
map-cong f≗g nothing  = refl

map-cong-local : ∀ {f g : A → B} {mx} →
  All (λ x → f x ≡ g x) mx → map f mx ≡ map g mx
map-cong-local (just eq) = cong just eq
map-cong-local nothing   = refl

map-injective : ∀ {f : A → B} → Injective _≡_ _≡_ f → Injective _≡_ _≡_ (map f)
map-injective f-inj {nothing} {nothing} p = refl
map-injective f-inj {just x} {just y} p = cong just (f-inj (just-injective p))

map-∘ : {g : B → C} {f : A → B} → map (g ∘ f) ≗ map g ∘ map f
map-∘ (just x) = refl
map-∘ nothing  = refl

map-nothing : ∀ {f : A → B} {ma} → ma ≡ nothing → map f ma ≡ nothing
map-nothing refl = refl

map-just : ∀ {f : A → B} {ma a} → ma ≡ just a → map f ma ≡ just (f a)
map-just refl = refl

------------------------------------------------------------------------
-- maybe

maybe-map : ∀ {C : Maybe B → Set c}
            (j : (x : B) → C (just x)) (n : C nothing) (f : A → B) ma →
            maybe {B = C} j n (map f ma) ≡ maybe {B = C ∘ map f} (j ∘ f) n ma
maybe-map j n f (just x) = refl
maybe-map j n f nothing  = refl

maybe′-map : ∀ j (n : C) (f : A → B) ma →
             maybe′ j n (map f ma) ≡ maybe′ (j ∘′ f) n ma
maybe′-map = maybe-map

------------------------------------------------------------------------
-- _<∣>_

module _ {A : Set a} where

  open Definitions {A = Maybe A} _≡_

  <∣>-assoc : Associative _<∣>_
  <∣>-assoc (just x) y z = refl
  <∣>-assoc nothing  y z = refl

  <∣>-identityˡ : LeftIdentity nothing _<∣>_
  <∣>-identityˡ (just x) = refl
  <∣>-identityˡ nothing  = refl

  <∣>-identityʳ : RightIdentity nothing _<∣>_
  <∣>-identityʳ (just x) = refl
  <∣>-identityʳ nothing  = refl

  <∣>-identity : Identity nothing _<∣>_
  <∣>-identity = <∣>-identityˡ , <∣>-identityʳ

  <∣>-idem : Idempotent _<∣>_
  <∣>-idem (just x) = refl
  <∣>-idem nothing = refl

module _ (A : Set a) where

  open Structures {A = Maybe A} _≡_

  <∣>-isMagma : IsMagma _<∣>_
  <∣>-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong        = cong₂ _<∣>_
    }

  <∣>-isSemigroup : IsSemigroup _<∣>_
  <∣>-isSemigroup = record
    { isMagma = <∣>-isMagma
    ; assoc   = <∣>-assoc
    }

  <∣>-isMonoid : IsMonoid _<∣>_ nothing
  <∣>-isMonoid = record
    { isSemigroup = <∣>-isSemigroup
    ; identity    = <∣>-identity
    }

  <∣>-semigroup : Semigroup a a
  <∣>-semigroup = record
    { isSemigroup = <∣>-isSemigroup
    }

  <∣>-monoid : Monoid a a
  <∣>-monoid = record
    { isMonoid = <∣>-isMonoid
    }

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

map-id₂ = map-id-local
{-# WARNING_ON_USAGE map-id₂
"Warning: map-id₂ was deprecated in v2.0.
Please use map-id-local instead."
#-}

map-cong₂ = map-cong-local
{-# WARNING_ON_USAGE map-id₂
"Warning: map-cong₂ was deprecated in v2.0.
Please use map-cong-local instead."
#-}

map-compose = map-∘
{-# WARNING_ON_USAGE map-compose
"Warning: map-compose was deprecated in v2.0.
Please use map-∘ instead."
#-}

map-<∣>-commute = map-<∣>
{-# WARNING_ON_USAGE map-<∣>-commute
"Warning: map-<∣>-commute was deprecated in v2.0.
Please use map-<∣> instead."
#-}
