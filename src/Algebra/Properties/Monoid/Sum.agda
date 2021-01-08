------------------------------------------------------------------------
-- The Agda standard library
--
-- Finite summations over a monoid
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Monoid)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; NonZero)
open import Data.Vec.Functional as Vector
open import Data.Fin.Base using (zero; suc)
open import Data.Unit using (tt)
open import Function.Base using (_∘_)
open import Relation.Binary as B using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality as P using (_≗_; _≡_)

module Algebra.Properties.Monoid.Sum {a ℓ} (M : Monoid a ℓ) where

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

------------------------------------------------------------------------
-- Definition

open import Algebra.Definitions.RawMonoid rawMonoid public
  using (sum)

------------------------------------------------------------------------
-- An alternative mathematical-style syntax for sumₜ

infixl 10 sum-syntax

sum-syntax : ∀ n → Vector Carrier n → Carrier
sum-syntax _ = sum

syntax sum-syntax n (λ i → x) = ∑[ i < n ] x

------------------------------------------------------------------------
-- Properties

sum-cong-≋ : ∀ {n} → sum {n} Preserves _≋_ ⟶ _≈_
sum-cong-≋ {zero}  xs≋ys = refl
sum-cong-≋ {suc n} xs≋ys = +-cong (xs≋ys zero) (sum-cong-≋ (xs≋ys ∘ suc))

sum-cong-≗ : ∀ {n} → sum {n} Preserves _≗_ ⟶ _≡_
sum-cong-≗ {zero}  xs≗ys = P.refl
sum-cong-≗ {suc n} xs≗ys = P.cong₂ _+_ (xs≗ys zero) (sum-cong-≗ (xs≗ys ∘ suc))

sum-replicate : ∀ n {x} → sum {n} (replicate x) ≈ n × x
sum-replicate zero    = refl
sum-replicate (suc n) = +-congˡ (sum-replicate n)

sum-replicate-idem : ∀ {x} → _+_ IdempotentOn x →
                     ∀ n → .{{_ : NonZero n}} → sum {n} (replicate x) ≈ x
sum-replicate-idem idem n = trans (sum-replicate n) (×-idem idem n)

sum-replicate-zero : ∀ n → sum {n} (replicate 0#) ≈ 0#
sum-replicate-zero zero    = refl
sum-replicate-zero (suc n) = sum-replicate-idem (+-identityˡ 0#) (suc n)
