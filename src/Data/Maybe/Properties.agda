------------------------------------------------------------------------
-- The Agda standard library
--
-- Maybe-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

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
open import Relation.Nullary using (yes; no)
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

map-id₂ : ∀ {f : A → A} {mx} → All (λ x → f x ≡ x) mx → map f mx ≡ mx
map-id₂ (just eq) = cong just eq
map-id₂ nothing   = refl

map-<∣>-commute : ∀ (f : A → B) mx my →
  map f (mx <∣> my) ≡ map f mx <∣> map f my
map-<∣>-commute f (just x) my = refl
map-<∣>-commute f nothing  my = refl

map-cong : {f g : A → B} → f ≗ g → map f ≗ map g
map-cong f≗g (just x) = cong just (f≗g x)
map-cong f≗g nothing  = refl

map-cong₂ : ∀ {f g : A → B} {mx} →
  All (λ x → f x ≡ g x) mx → map f mx ≡ map g mx
map-cong₂ (just eq) = cong just eq
map-cong₂ nothing   = refl

map-compose : {g : B → C} {f : A → B} → map (g ∘ f) ≗ map g ∘ map f
map-compose (just x) = refl
map-compose nothing  = refl

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
