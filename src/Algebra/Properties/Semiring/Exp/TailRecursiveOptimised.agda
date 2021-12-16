------------------------------------------------------------------------
-- The Agda standard library
--
-- Exponentiation over a semiring optimised for tail-recursion.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Data.Nat.Base as ℕ using (zero; suc)
import Data.Nat.Properties as ℕ
open import Relation.Binary

module Algebra.Properties.Semiring.Exp.TailRecursiveOptimised
  {a ℓ} (S : Semiring a ℓ) where

open Semiring S renaming (zero to *-zero)
open import Relation.Binary.Reasoning.Setoid setoid
open import Algebra.Properties.Semiring.Exp S as U
  using (_^_)

------------------------------------------------------------------------
-- Re-export definition from the monoid

open import Algebra.Definitions.RawSemiring rawSemiring public
  using (_^[_]*_; _^ᵗ_)

------------------------------------------------------------------------
-- Properties of _^[_]*_

^[]*-cong : ∀ n → (_^[ n ]*_) Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
^[]*-cong zero    x≈y u≈v = u≈v
^[]*-cong (suc n) x≈y u≈v = ^[]*-cong n x≈y (*-cong x≈y u≈v)

^[]*-congʳ : ∀ x n → (x ^[ n ]*_) Preserves _≈_ ⟶ _≈_
^[]*-congʳ x n = ^[]*-cong n refl

x^[m]*[x*y]≈x*x^[m]*y : ∀ x m y → x ^[ m ]* (x * y) ≈ x * x ^[ m ]* y
x^[m]*[x*y]≈x*x^[m]*y x zero    y = refl
x^[m]*[x*y]≈x*x^[m]*y x (suc m) y = x^[m]*[x*y]≈x*x^[m]*y x m (x * y)

x^[m]*y*z≈x^[m]*[y*z] : ∀ x m y z → x ^[ m ]* y * z ≈ x ^[ m ]* (y * z)
x^[m]*y*z≈x^[m]*[y*z] x zero    y z = refl
x^[m]*y*z≈x^[m]*[y*z] x (suc m) y z = begin
  x ^[ suc m ]* y * z     ≈⟨ x^[m]*y*z≈x^[m]*[y*z] x m (x * y) z ⟩
  x ^[ m ]* ((x * y) * z) ≈⟨ ^[]*-congʳ x m (*-assoc x y z) ⟩
  x ^[ m ]* (x * (y * z)) ∎

x^[m+n]*y≈x^[m]*x^[n]*y : ∀ x m n y → x ^[ (m  ℕ.+ n) ]* y ≈ x ^[ m ]* x ^[ n ]* y
x^[m+n]*y≈x^[m]*x^[n]*y x zero    n y = refl
x^[m+n]*y≈x^[m]*x^[n]*y x (suc m) n y = begin
  x ^[ (m  ℕ.+ n) ]* (x * y) ≈⟨ x^[m+n]*y≈x^[m]*x^[n]*y x m n (x * y) ⟩
  x ^[ m ]* x ^[ n ]* (x * y) ≈⟨ ^[]*-congʳ x m (x^[m]*[x*y]≈x*x^[m]*y x n y) ⟩
  x ^[ suc m ]* x ^[ n ]* y   ∎

x^ᵗm*y≈x^[m]*y : ∀ x m y → x ^ᵗ m * y ≈ x ^[ m ]* y
x^ᵗm*y≈x^[m]*y x m y = begin
  x ^ᵗ m * y         ≈⟨ x^[m]*y*z≈x^[m]*[y*z] x m 1# y ⟩
  x ^[ m ]* (1# * y) ≈⟨ ^[]*-congʳ x m (*-identityˡ y) ⟩
  x ^[ m ]* y        ∎

------------------------------------------------------------------------
-- Properties of _^ᵗ_

x^ᵗ0≈1 : ∀ x → x ^ᵗ zero ≈ 1#
x^ᵗ0≈1 x = refl

x^ᵗ[m+1]≈x*[x^ᵗm] : ∀ x m → x ^ᵗ (suc m) ≈ x * x ^ᵗ m
x^ᵗ[m+1]≈x*[x^ᵗm] x m = x^[m]*[x*y]≈x*x^[m]*y x m 1#

x^ᵗ[m+n]≈[x^ᵗm]*[x^ᵗn] : ∀ x m n → x ^ᵗ (m ℕ.+ n) ≈ x ^ᵗ m * x ^ᵗ n
x^ᵗ[m+n]≈[x^ᵗm]*[x^ᵗn] x m n = begin
  x ^ᵗ (m  ℕ.+ n)   ≈⟨ x^[m+n]*y≈x^[m]*x^[n]*y x m n 1# ⟩
  x ^[ m ]* (x ^ᵗ n) ≈˘⟨ x^ᵗm*y≈x^[m]*y x m (x ^ᵗ n) ⟩
  x ^ᵗ m * x ^ᵗ n    ∎

^ᵗ≈^ : ∀ x m → x ^ᵗ m ≈ x ^ m
^ᵗ≈^ x zero    = refl
^ᵗ≈^ x (suc m) = begin
  x ^ᵗ (suc m) ≈⟨ x^ᵗ[m+1]≈x*[x^ᵗm] x m ⟩
  x * x ^ᵗ m   ≈⟨ *-congˡ (^ᵗ≈^ x m) ⟩
  x * x ^ m   ∎
