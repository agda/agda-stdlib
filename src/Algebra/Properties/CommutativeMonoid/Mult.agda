------------------------------------------------------------------------
-- The Agda standard library
--
-- Multiplication over a monoid (i.e. repeated addition)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (CommutativeMonoid)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)

module Algebra.Properties.CommutativeMonoid.Mult
  {a ℓ} (M : CommutativeMonoid a ℓ) where

-- View of the monoid operator as addition
open CommutativeMonoid M
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
open import Algebra.Properties.CommutativeSemigroup commutativeSemigroup

------------------------------------------------------------------------
-- Re-export definition and properties for monoids

open import Algebra.Properties.Monoid.Mult monoid public

------------------------------------------------------------------------
-- Properties of _×_

×-distrib-+ : ∀ x y n → n × (x + y) ≈ n × x + n × y
×-distrib-+ x y zero    = sym (+-identityˡ 0# )
×-distrib-+ x y (suc n) = begin
  x + y + n × (x + y)       ≈⟨ +-congˡ (×-distrib-+ x y n) ⟩
  x + y + (n × x + n × y)   ≈⟨ +-assoc x y (n × x + n × y) ⟩
  x + (y + (n × x + n × y)) ≈⟨ +-congˡ (x∙yz≈y∙xz y (n × x) (n × y)) ⟩
  x + (n × x + suc n × y)   ≈⟨ x∙yz≈xy∙z x (n × x) (suc n × y) ⟩
  suc n × x + suc n × y     ∎
