------------------------------------------------------------------------
-- The Agda standard library
--
-- Some defined operations (multiplication by natural number and
-- exponentiation)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Disabled to prevent warnings from deprecated Table
{-# OPTIONS --warn=noUserWarning #-}

open import Algebra

module Algebra.Operations.CommutativeMonoid
  {s₁ s₂} (CM : CommutativeMonoid s₁ s₂)
  where

open import Data.Nat.Base using (ℕ; zero; suc)
  renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.Fin.Base using (Fin; zero)
open import Data.Product using (proj₁; proj₂)
open import Data.Table.Base as Table using (Table)
open import Function using (_∘_; _⟨_⟩_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open CommutativeMonoid CM
  renaming
  ( _∙_       to _+_
  ; ∙-cong    to +-cong
  ; identityˡ to +-identityˡ
  ; identityʳ to +-identityʳ
  ; assoc     to +-assoc
  ; comm      to +-comm
  ; ε         to 0#
  )
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Operations

-- Multiplication by natural number.

infixr 8 _×_ _×′_

_×_ : ℕ → Carrier → Carrier
0     × x = 0#
suc n × x = x + n × x

-- A variant that includes a "redundant" case which ensures that `1 × x`
-- is definitionally equal to `x`.

_×′_ : ℕ → Carrier → Carrier
0     ×′ x = 0#
1     ×′ x = x
suc n ×′ x = x + n ×′ x

-- Summation over lists/tables

sumₗ : List Carrier → Carrier
sumₗ = List.foldr _+_ 0#

sumₜ : ∀ {n} → Table Carrier n → Carrier
sumₜ = Table.foldr _+_ 0#

-- An alternative mathematical-style syntax for sumₜ

infixl 10 sumₜ-syntax

sumₜ-syntax : ∀ n → (Fin n → Carrier) → Carrier
sumₜ-syntax _ = sumₜ ∘ Table.tabulate

syntax sumₜ-syntax n (λ i → x) = ∑[ i < n ] x

------------------------------------------------------------------------
-- Properties of _×_

×-congʳ : ∀ n → (n ×_) Preserves _≈_ ⟶ _≈_
×-congʳ 0       x≈x′ = refl
×-congʳ (suc n) x≈x′ = x≈x′ ⟨ +-cong ⟩ ×-congʳ n x≈x′

×-cong : _×_ Preserves₂ _≡_ ⟶ _≈_ ⟶ _≈_
×-cong {u} P.refl x≈x′ = ×-congʳ u x≈x′

-- _×_ is homomorphic with respect to _ℕ+_/_+_.

×-homo-+ : ∀ c m n → (m ℕ+ n) × c ≈ m × c + n × c
×-homo-+ c 0       n = sym (+-identityˡ (n × c))
×-homo-+ c (suc m) n = begin
  c + (m ℕ+ n) × c     ≈⟨ +-cong refl (×-homo-+ c m n) ⟩
  c + (m × c + n × c)  ≈⟨ sym (+-assoc c (m × c) (n × c)) ⟩
  c + m × c + n × c    ∎

------------------------------------------------------------------------
-- Properties of _×′_

1+×′ : ∀ n x → suc n ×′ x ≈ x + n ×′ x
1+×′ 0       x = sym (+-identityʳ x)
1+×′ (suc n) x = refl

-- _×_ and _×′_ are extensionally equal (up to the setoid
-- equivalence).

×≈×′ : ∀ n x → n × x ≈ n ×′ x
×≈×′ 0       x = begin 0# ∎
×≈×′ (suc n) x = begin
  x + n × x   ≈⟨ +-cong refl (×≈×′ n x) ⟩
  x + n ×′ x  ≈⟨ sym (1+×′ n x) ⟩
  suc n ×′ x  ∎

-- _×′_ is homomorphic with respect to _ℕ+_/_+_.

×′-homo-+ : ∀ c m n → (m ℕ+ n) ×′ c ≈ m ×′ c + n ×′ c
×′-homo-+ c m n = begin
  (m ℕ+ n) ×′ c    ≈⟨ sym (×≈×′ (m ℕ+ n) c) ⟩
  (m ℕ+ n) ×  c    ≈⟨ ×-homo-+ c m n ⟩
  m ×  c + n ×  c  ≈⟨ +-cong (×≈×′ m c) (×≈×′ n c) ⟩
  m ×′ c + n ×′ c  ∎

-- _×′_ preserves equality.

×′-cong : _×′_ Preserves₂ _≡_ ⟶ _≈_ ⟶ _≈_
×′-cong {n} {_} {x} {y} P.refl x≈y = begin
  n  ×′ x ≈⟨ sym (×≈×′ n x) ⟩
  n  ×  x ≈⟨ ×-congʳ n x≈y ⟩
  n  ×  y ≈⟨ ×≈×′ n y ⟩
  n  ×′ y ∎
