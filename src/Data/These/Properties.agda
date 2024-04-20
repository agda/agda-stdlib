------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of These
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.These.Properties where

open import Data.Product.Base using (_×_; _,_; <_,_>; uncurry)
open import Data.These.Base using (These; this; that; these)
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; cong₂)
open import Relation.Nullary.Decidable using (yes; no; map′; _×-dec_)

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

  ≡-dec : DecidableEquality A → DecidableEquality B → DecidableEquality (These A B)
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
