------------------------------------------------------------------------
-- The Agda standard library
--
-- Maybe-related properties
------------------------------------------------------------------------

module Data.Maybe.Properties where

open import Algebra
open import Algebra.Structures
open import Algebra.FunctionProperties
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
-- _<∣>_

module _ {a} {A : Set a} where

  <∣>-assoc : Associative {A = Maybe A} _≡_ _<∣>_
  <∣>-assoc (just x) y z = refl
  <∣>-assoc nothing  y z = refl

  <∣>-identityˡ : LeftIdentity {A = Maybe A} _≡_ nothing _<∣>_
  <∣>-identityˡ (just x) = refl
  <∣>-identityˡ nothing  = refl

  <∣>-identityʳ : RightIdentity {A = Maybe A} _≡_ nothing _<∣>_
  <∣>-identityʳ (just x) = refl
  <∣>-identityʳ nothing  = refl

  <∣>-identity : Identity {A = Maybe A} _≡_ nothing _<∣>_
  <∣>-identity = <∣>-identityˡ , <∣>-identityʳ

module _ {a} (A : Set a) where

  <∣>-isSemigroup : IsSemigroup {A = Maybe A} _≡_ _<∣>_
  <∣>-isSemigroup = record
    { isEquivalence = isEquivalence
    ; assoc         = <∣>-assoc
    ; ∙-cong        = cong₂ _<∣>_
    }

  <∣>-isMonoid : IsMonoid {A = Maybe A} _≡_ _<∣>_ nothing
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
