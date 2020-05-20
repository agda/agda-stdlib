------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of products
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Properties where

open import Axiom.UniquenessOfIdentityProofs
open import Data.Product
open import Function using (_∘_;_∋_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Product
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- Equality (dependent)

module _ {a b} {A : Set a} {B : A → Set b} where

  ,-injectiveˡ : ∀ {a c} {b : B a} {d : B c} → (a , b) ≡ (c , d) → a ≡ c
  ,-injectiveˡ refl = refl

  ,-injectiveʳ-≡ : ∀ {a b} {c : B a} {d : B b} → UIP A → (a , c) ≡ (b , d) → (q : a ≡ b) → subst B q c ≡ d
  ,-injectiveʳ-≡ {c = c} u refl q = cong (λ x → subst B x c) (u q refl)

  ,-injectiveʳ-UIP : ∀ {a} {b c : B a} → UIP A → (Σ A B ∋ (a , b)) ≡ (a , c) → b ≡ c
  ,-injectiveʳ-UIP u p = ,-injectiveʳ-≡ u p refl

  ≡-dec : DecidableEquality A → (∀ {a} → DecidableEquality (B a)) →
          DecidableEquality (Σ A B)
  ≡-dec dec₁ dec₂ (a , x) (b , y) with dec₁ a b
  ... | no [a≢b] = no ([a≢b] ∘ ,-injectiveˡ)
  ... | yes refl = Dec.map′ (cong (a ,_)) (,-injectiveʳ-UIP (Decidable⇒UIP.≡-irrelevant dec₁)) (dec₂ x y)

------------------------------------------------------------------------
-- Equality (non-dependent)

module _ {a b} {A : Set a} {B : Set b} where

  ,-injectiveʳ : ∀ {a c : A} {b d : B} → (a , b) ≡ (c , d) → b ≡ d
  ,-injectiveʳ refl = refl

  ,-injective : ∀ {a c : A} {b d : B} → (a , b) ≡ (c , d) → a ≡ c × b ≡ d
  ,-injective refl = refl , refl
