------------------------------------------------------------------------
-- The Agda standard library
--
-- Multiplication over a monoid (i.e. repeated addition)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Monoid)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; NonZero)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module Algebra.Properties.Monoid.Mult {a ℓ} (M : Monoid a ℓ) where

-- View of the monoid operator as addition
open Monoid M
  renaming
  ( _∙_       to _+_
  ; ∙-cong    to +-cong
  ; ∙-congʳ   to +-congʳ
  ; ∙-congˡ   to +-congˡ
  ; identityˡ to +-identityˡ
  ; identityʳ to +-identityʳ
  ; assoc     to +-assoc
  ; ε         to 0#
  )

open import Relation.Binary.Reasoning.Setoid setoid

open import Algebra.Definitions _≈_

------------------------------------------------------------------------
-- Definition

open import Algebra.Definitions.RawMonoid rawMonoid public
  using (_×_)

------------------------------------------------------------------------
-- Properties of _×_

×-congʳ : ∀ n → (n ×_) Preserves _≈_ ⟶ _≈_
×-congʳ 0       x≈x′ = refl
×-congʳ (suc n) x≈x′ = +-cong x≈x′ (×-congʳ n x≈x′)

×-cong : _×_ Preserves₂ _≡_ ⟶ _≈_ ⟶ _≈_
×-cong {n} P.refl x≈x′ = ×-congʳ n x≈x′

-- _×_ is homomorphic with respect to _ℕ+_/_+_.

×-homo-+ : ∀ x m n → (m ℕ.+ n) × x ≈ m × x + n × x
×-homo-+ x 0       n = sym (+-identityˡ (n × x))
×-homo-+ x (suc m) n = begin
  x + (m ℕ.+ n) × x    ≈⟨ +-cong refl (×-homo-+ x m n) ⟩
  x + (m × x + n × x)  ≈⟨ sym (+-assoc x (m × x) (n × x)) ⟩
  x + m × x + n × x    ∎

×-idem : ∀ {c} → _+_ IdempotentOn c →
         ∀ n → .{{_ : NonZero n}} → n × c ≈ c
×-idem {c} idem (suc zero)    = +-identityʳ c
×-idem {c} idem (suc (suc n)) = begin
  c + (suc n × c) ≈⟨ +-congˡ (×-idem idem (suc n) ) ⟩
  c + c           ≈⟨ idem ⟩
  c               ∎

×-assocˡ : ∀ x m n → m × (n × x) ≈ (m ℕ.* n) × x
×-assocˡ x zero    n = refl
×-assocˡ x (suc m) n = begin
  n × x + m × n × x     ≈⟨ +-congˡ (×-assocˡ x m n) ⟩
  n × x + (m ℕ.* n) × x ≈˘⟨ ×-homo-+ x n (m ℕ.* n) ⟩
  (suc m ℕ.* n) × x     ∎
