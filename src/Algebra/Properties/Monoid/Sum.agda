------------------------------------------------------------------------
-- The Agda standard library
--
-- Finite summations over a monoid
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Monoid)

module Algebra.Properties.Monoid.Sum {a ℓ} (M : Monoid a ℓ) where

open import Data.Nat.Base as ℕ using (ℕ; zero; suc; NonZero)
open import Data.Vec.Functional as Vector using (Vector; replicate; init;
  last; head; tail)
open import Data.Fin.Base using (zero; suc)
open import Function.Base using (_∘_)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≗_; _≡_)

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

open import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid
open import Algebra.Properties.Monoid.Mult M
open import Algebra.Definitions _≈_
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Definition

open import Algebra.Definitions.RawMonoid rawMonoid public
  using (sum)

------------------------------------------------------------------------
-- An alternative mathematical-style syntax for sumₜ

infixl 10 sum-syntax sum⁺-syntax

sum-syntax : ∀ n → Vector Carrier n → Carrier
sum-syntax _ = sum

syntax sum-syntax n (λ i → x) = ∑[ i < n ] x

sum⁺-syntax = sum-syntax ∘ suc

syntax sum⁺-syntax n (λ i → x) = ∑[ i ≤ n ] x

------------------------------------------------------------------------
-- Properties

sum-cong-≋ : ∀ {n} → sum {n} Preserves _≋_ ⟶ _≈_
sum-cong-≋ {zero}  xs≋ys = refl
sum-cong-≋ {suc n} xs≋ys = +-cong (xs≋ys zero) (sum-cong-≋ (xs≋ys ∘ suc))

sum-cong-≗ : ∀ {n} → sum {n} Preserves _≗_ ⟶ _≡_
sum-cong-≗ {zero}  xs≗ys = ≡.refl
sum-cong-≗ {suc n} xs≗ys = ≡.cong₂ _+_ (xs≗ys zero) (sum-cong-≗ (xs≗ys ∘ suc))

sum-replicate : ∀ n {x} → sum (replicate n x) ≈ n × x
sum-replicate zero    = refl
sum-replicate (suc n) = +-congˡ (sum-replicate n)

sum-replicate-idem : ∀ {x} → _+_ IdempotentOn x →
                     ∀ n → .{{_ : NonZero n}} → sum (replicate n x) ≈ x
sum-replicate-idem idem n = trans (sum-replicate n) (×-idem idem n)

sum-replicate-zero : ∀ n → sum (replicate n 0#) ≈ 0#
sum-replicate-zero zero    = refl
sum-replicate-zero (suc n) = sum-replicate-idem (+-identityˡ 0#) (suc n)

-- When summing over a `Vector`, we can pull out last element

sum-init-last : ∀ {n} (t : Vector Carrier (suc n)) → sum t ≈ sum (init t) + last t
sum-init-last {zero} t  = begin
  t₀ + 0# ≈⟨ +-identityʳ t₀ ⟩
  t₀      ≈⟨ +-identityˡ t₀ ⟨
  0# + t₀ ∎ where t₀ = t zero
sum-init-last {suc n} t = begin
  t₀ + ∑t             ≈⟨ +-congˡ (sum-init-last (tail t)) ⟩
  t₀ + (∑t′ + tₗ)     ≈⟨ +-assoc _ _ _ ⟨
  (t₀ + ∑t′) + tₗ     ∎
  where
    t₀ = head t
    tₗ = last t
    ∑t = sum (tail t)
    ∑t′ = sum (tail (init t))
