------------------------------------------------------------------------
-- The Agda standard library
--
-- Multiplication over a monoid (i.e. repeated addition) optimised for
-- type checking.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Monoid)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Relation.Binary.Core using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module Algebra.Properties.Monoid.Multiplication.TCOptimised
  {a ℓ} (M : Monoid a ℓ) where

open Monoid M renaming
  ( _∙_       to _+_
  ; ∙-cong    to +-cong
  ; ∙-congˡ   to +-congˡ
  ; identityˡ to +-identityˡ
  ; identityʳ to +-identityʳ
  ; assoc     to +-assoc
  ; ε         to 0#
  )

open import Algebra.Properties.Monoid.Multiplication M as U
  using () renaming (_×_ to _×ᵤ_)

open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Definition

open import Algebra.Definitions.RawMonoid rawMonoid public
  using () renaming (_×′_ to _×_)

------------------------------------------------------------------------
-- Properties of _×′_

1+× : ∀ n x → suc n × x ≈ x + n × x
1+× 0       x = sym (+-identityʳ x)
1+× (suc n) x = refl

-- The unoptimised (_×ᵤ_) and optimised (_×_) versions of multiplication
-- are extensionally equal (up to the setoid equivalence).

×ᵤ≈× : ∀ n x → n ×ᵤ x ≈ n × x
×ᵤ≈× 0       x = refl
×ᵤ≈× (suc n) x = begin
  x + n ×ᵤ x  ≈⟨ +-congˡ (×ᵤ≈× n x) ⟩
  x + n ×  x  ≈˘⟨ 1+× n x ⟩
  suc n ×  x  ∎

-- _×_ is homomorphic with respect to _ℕ.+_/_+_.

×-homo-+ : ∀ c m n → (m ℕ.+ n) × c ≈ m × c + n × c
×-homo-+ c m n = begin
  (m ℕ.+ n) ×  c   ≈˘⟨ ×ᵤ≈× (m ℕ.+ n) c ⟩
  (m ℕ.+ n) ×ᵤ c   ≈⟨ U.×-homo-+ c m n ⟩
  m ×ᵤ c + n ×ᵤ c  ≈⟨ +-cong (×ᵤ≈× m c) (×ᵤ≈× n c) ⟩
  m ×  c + n ×  c  ∎

-- _×_ preserves equality.

×-cong : _×_ Preserves₂ _≡_ ⟶ _≈_ ⟶ _≈_
×-cong {n} {_} {x} {y} P.refl x≈y = begin
  n  ×  x ≈˘⟨ ×ᵤ≈× n x ⟩
  n  ×ᵤ x ≈⟨  U.×-congʳ n x≈y ⟩
  n  ×ᵤ y ≈⟨  ×ᵤ≈× n y ⟩
  n  ×  y ∎
