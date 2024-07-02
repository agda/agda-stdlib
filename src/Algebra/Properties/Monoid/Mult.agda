------------------------------------------------------------------------
-- The Agda standard library
--
-- Multiplication over a monoid (i.e. repeated addition)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Monoid)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; NonZero)
open import Relation.Binary.Core using (_Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

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
  using (_×_; _×′_)

------------------------------------------------------------------------
-- Properties of _×_

×-congʳ : ∀ n → (n ×_) Preserves _≈_ ⟶ _≈_
×-congʳ 0       x≈x′ = refl
×-congʳ (suc n) x≈x′ = +-cong x≈x′ (×-congʳ n x≈x′)

×-cong : _×_ Preserves₂ _≡_ ⟶ _≈_ ⟶ _≈_
×-cong {n} ≡.refl x≈x′ = ×-congʳ n x≈x′

×-congˡ : ∀ {x} → (_× x) Preserves _≡_ ⟶ _≈_
×-congˡ m≡n = ×-cong m≡n refl

-- _×_ is homomorphic with respect to _ℕ+_/_+_.

×-homo-0 : ∀ x → 0 × x ≈ 0#
×-homo-0 x = refl

×-homo-1 : ∀ x → 1 × x ≈ x
×-homo-1 = +-identityʳ

×-homo-+ : ∀ x m n → (m ℕ.+ n) × x ≈ m × x + n × x
×-homo-+ x 0       n = sym (+-identityˡ (n × x))
×-homo-+ x (suc m) n = begin
  x + (m ℕ.+ n) × x    ≈⟨ +-congˡ (×-homo-+ x m n) ⟩
  x + (m × x + n × x)  ≈⟨ +-assoc x (m × x) (n × x) ⟨
  x + m × x + n × x    ∎

×-idem : ∀ {c} → _+_ IdempotentOn c →
         ∀ n → .{{_ : NonZero n}} → n × c ≈ c
×-idem {c} idem (suc zero)    = +-identityʳ c
×-idem {c} idem (suc n@(suc _)) = begin
  c + (n × c) ≈⟨ +-congˡ (×-idem idem n ) ⟩
  c + c       ≈⟨ idem ⟩
  c           ∎

×-assocˡ : ∀ x m n → m × (n × x) ≈ (m ℕ.* n) × x
×-assocˡ x zero    n = refl
×-assocˡ x (suc m) n = begin
  n × x + m × n × x     ≈⟨ +-congˡ (×-assocˡ x m n) ⟩
  n × x + (m ℕ.* n) × x ≈⟨ ×-homo-+ x n (m ℕ.* n) ⟨
  (suc m ℕ.* n) × x     ∎

------------------------------------------------------------------------
-- Properties of _×′_

1+×′ : ∀ n x → suc n ×′ x ≈ x + n ×′ x
1+×′ 0               x = sym (+-identityʳ x)
1+×′ 1               x = refl
1+×′ (suc n@(suc _)) x = begin
  suc n ×′ x + x ≈⟨ +-congʳ (1+×′ n x) ⟩
  x + n ×′ x + x ≈⟨ +-assoc x (n ×′ x) x ⟩
  x + (suc n) ×′ x ∎

-- _×′_ and _×_ are extensionally equal (up to setoid equivalence).

×′≈× : ∀ n x → n ×′ x ≈ n × x
×′≈× 0               x = refl
×′≈× 1               x = sym (×-homo-1 x)
×′≈× (suc n@(suc _)) x = begin
  n ×′ x + x  ≈⟨ 1+×′ n x ⟩
  x + n ×′ x  ≈⟨ +-congˡ (×′≈× n x) ⟩
  suc n × x   ∎

