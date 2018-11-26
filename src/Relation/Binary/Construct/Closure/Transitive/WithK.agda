------------------------------------------------------------------------
-- The Agda standard library
--
-- Some code related to transitive closures that relies on the K rule
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}

module Relation.Binary.Construct.Closure.Transitive.WithK where

open import Function
open import Relation.Binary
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module _ {a ℓ} {A : Set a} {_∼_ : Rel A ℓ} where

 ∼⁺⟨⟩-injectiveˡ : ∀ {x y z} {p r : x [ _∼_ ]⁺ y} {q s} →
                   (x [ _∼_ ]⁺ z ∋ x ∼⁺⟨ p ⟩ q) ≡ (x ∼⁺⟨ r ⟩ s) → p ≡ r
 ∼⁺⟨⟩-injectiveˡ refl = refl

 ∼⁺⟨⟩-injectiveʳ : ∀ {x y z} {p r : x [ _∼_ ]⁺ y} {q s} →
                   (x [ _∼_ ]⁺ z ∋ x ∼⁺⟨ p ⟩ q) ≡ (x ∼⁺⟨ r ⟩ s) → q ≡ s
 ∼⁺⟨⟩-injectiveʳ refl = refl
