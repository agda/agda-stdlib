------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of These
------------------------------------------------------------------------

module Data.These.Properties where

open import Data.These
open import Function using (_∘_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)

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

  ≡-dec : Decidable _≡_ → Decidable _≡_ → Decidable {A = These A B} _≡_
  ≡-dec dec₁ dec₂ (this x)    (this y)    with dec₁ x y
  ... | yes refl = yes refl
  ... | no  x≢y  = no (x≢y ∘ this-injective)
  ≡-dec dec₁ dec₂ (this x)    (that y)    = no λ()
  ≡-dec dec₁ dec₂ (this x)    (these y b) = no λ()
  ≡-dec dec₁ dec₂ (that x)    (this y)    = no λ()
  ≡-dec dec₁ dec₂ (that x)    (that y)    with dec₂ x y
  ... | yes refl = yes refl
  ... | no  x≢y  = no (x≢y ∘ that-injective)
  ≡-dec dec₁ dec₂ (that x)    (these y b) = no λ()
  ≡-dec dec₁ dec₂ (these x a) (this y)    = no λ()
  ≡-dec dec₁ dec₂ (these x a) (that y)    = no λ()
  ≡-dec dec₁ dec₂ (these x a) (these y b) with dec₁ x y | dec₂ a b
  ... | yes refl | yes refl = yes refl
  ... | no  x≢y  | _        = no (x≢y ∘ these-injectiveˡ)
  ... | yes _    | no  a≢b  = no (a≢b ∘ these-injectiveʳ)
