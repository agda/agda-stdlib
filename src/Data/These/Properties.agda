------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of These
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.These.Properties where

open import Data.Product
open import Data.These.Base
open import Function using (_∘_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Nullary.Product using (_×-dec_)

------------------------------------------------------------------------
-- Equality

module _ {a b} {A : Set a} {B : Set b} where

  this-injective : ∀ {x y : A} → this {B = B} x ≡ this y → x ≡ y
  this-injective refl = refl

  that-injective : ∀ {a b : B} → that {A = A} a ≡ that b → a ≡ b
  that-injective refl = refl

  these-injectiveˡ : ∀ {x y : A} {a b : B} → these x a ≡ these y b → x ≡ y
  these-injectiveˡ refl = refl

  these-injectiveʳ : ∀ {x y : A} {a b : B} → these x a ≡ these y b → a ≡ b
  these-injectiveʳ refl = refl

  these-injective : ∀ {x y : A} {a b : B} → these x a ≡ these y b → x ≡ y × a ≡ b
  these-injective = < these-injectiveˡ , these-injectiveʳ >

  ≡-dec : Decidable _≡_ → Decidable _≡_ → Decidable {A = These A B} _≡_
  ≡-dec dec₁ dec₂ (this x)    (this y) =
    map′ (cong this) this-injective (dec₁ x y)
  ≡-dec dec₁ dec₂ (this x)    (that y)    = no λ()
  ≡-dec dec₁ dec₂ (this x)    (these y b) = no λ()
  ≡-dec dec₁ dec₂ (that x)    (this y)    = no λ()
  ≡-dec dec₁ dec₂ (that x)    (that y) =
    map′ (cong that) that-injective (dec₂ x y)
  ≡-dec dec₁ dec₂ (that x)    (these y b) = no λ()
  ≡-dec dec₁ dec₂ (these x a) (this y)    = no λ()
  ≡-dec dec₁ dec₂ (these x a) (that y)    = no λ()
  ≡-dec dec₁ dec₂ (these x a) (these y b) =
    map′ (uncurry (cong₂ these)) these-injective (dec₁ x y ×-dec dec₂ a b)
