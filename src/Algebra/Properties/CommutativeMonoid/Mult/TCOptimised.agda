------------------------------------------------------------------------
-- The Agda standard library
--
-- Multiplication over a monoid (i.e. repeated addition) optimised for
-- type checking.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (CommutativeMonoid)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Relation.Binary.Core using (_Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module Algebra.Properties.CommutativeMonoid.Mult.TCOptimised
  {a ℓ} (M : CommutativeMonoid a ℓ) where

open CommutativeMonoid M renaming
  ( _∙_       to _+_
  ; ∙-cong    to +-cong
  ; ∙-congˡ   to +-congˡ
  ; ∙-congʳ   to +-congʳ
  ; identityˡ to +-identityˡ
  ; identityʳ to +-identityʳ
  ; assoc     to +-assoc
  ; ε         to 0#
  )

open import Algebra.Properties.CommutativeMonoid.Mult M as U
  using () renaming (_×_ to _×ᵤ_)

open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Re-export definition and properties for monoids

open import Algebra.Properties.Monoid.Mult.TCOptimised monoid public

------------------------------------------------------------------------
-- Properties

×-distrib-+ : ∀ x y n → n × (x + y) ≈ n × x + n × y
×-distrib-+ x y n = begin
  n ×  (x + y)    ≈˘⟨ ×ᵤ≈× n (x + y) ⟩
  n ×ᵤ (x + y)    ≈⟨  U.×-distrib-+ x y n ⟩
  n ×ᵤ x + n ×ᵤ y ≈⟨  +-cong (×ᵤ≈× n x) (×ᵤ≈× n y) ⟩
  n ×  x + n ×  y ∎
