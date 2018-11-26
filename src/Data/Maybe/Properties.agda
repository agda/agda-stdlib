------------------------------------------------------------------------
-- The Agda standard library
--
-- Maybe-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Maybe.Properties where

open import Algebra
import Algebra.Structures as Structures
import Algebra.FunctionProperties as FunctionProperties
open import Data.Maybe.Base
open import Data.Maybe.All using (All; just; nothing)
open import Data.Product using (_,_)
open import Function

open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- just

module _ {a} {A : Set a} where

  just-injective : ∀ {x y} → (Maybe A ∋ just x) ≡ just y → x ≡ y
  just-injective refl = refl

------------------------------------------------------------------------
-- map

  map-id : map id ≗ id {A = Maybe A}
  map-id (just x) = refl
  map-id nothing  = refl

  map-id₂ : ∀ {f : A → A} {mx} → All (λ x → f x ≡ x) mx → map f mx ≡ mx
  map-id₂ (just eq) = cong just eq
  map-id₂ nothing   = refl

module _ {a b} {A : Set a} {B : Set b} where

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

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

  map-compose : {g : B → C} {f : A → B} → map (g ∘ f) ≗ map g ∘ map f
  map-compose (just x) = refl
  map-compose nothing  = refl

------------------------------------------------------------------------
-- maybe

module _ {a b} {A : Set a} {B : Set b} where

  maybe-map : ∀ {c} {C : Maybe B → Set c}
              (j : (x : B) → C (just x)) (n : C nothing) (f : A → B) ma →
              maybe {B = C} j n (map f ma) ≡ maybe {B = C ∘ map f} (j ∘ f) n ma
  maybe-map j n f (just x) = refl
  maybe-map j n f nothing  = refl

  maybe′-map : ∀ {c} {C : Set c} j (n : C) (f : A → B) ma →
               maybe′ j n (map f ma) ≡ maybe′ (j ∘′ f) n ma
  maybe′-map = maybe-map

------------------------------------------------------------------------
-- _<∣>_

module _ {a} {A : Set a} where

  open FunctionProperties {A = Maybe A} _≡_

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

module _ {a} (A : Set a) where

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
