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

module Algebra.Properties.Monoid.Multiplication {a ℓ} (M : Monoid a ℓ) where

-- View of the monoid operator as addition
open Monoid M
  renaming
  ( _∙_       to _+_
  ; ∙-cong    to +-cong
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
×-cong {u} P.refl x≈x′ = ×-congʳ u x≈x′

-- _×_ is homomorphic with respect to _ℕ+_/_+_.

×-homo-+ : ∀ c m n → (m ℕ.+ n) × c ≈ m × c + n × c
×-homo-+ c 0       n = sym (+-identityˡ (n × c))
×-homo-+ c (suc m) n = begin
  c + (m ℕ.+ n) × c    ≈⟨ +-cong refl (×-homo-+ c m n) ⟩
  c + (m × c + n × c)  ≈⟨ sym (+-assoc c (m × c) (n × c)) ⟩
  c + m × c + n × c    ∎

×-idem : ∀ {c} → _+_ IdempotentOn c →
         ∀ n → .{{_ : NonZero n}} → n × c ≈ c
×-idem {c} idem (suc zero)    = +-identityʳ c
×-idem {c} idem (suc (suc n)) = begin
  c + (suc n × c) ≈⟨ +-congˡ (×-idem idem (suc n) ) ⟩
  c + c           ≈⟨ idem ⟩
  c               ∎
