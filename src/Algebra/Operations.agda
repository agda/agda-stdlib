------------------------------------------------------------------------
-- The Agda standard library
--
-- Some defined operations (multiplication by natural number and
-- exponentiation)
------------------------------------------------------------------------

open import Algebra

module Algebra.Operations {s₁ s₂} (S : Semiring s₁ s₂) where

open import Data.Nat.Base
  using (zero; suc; ℕ) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Product using (module Σ)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.EqReasoning as EqR

open Semiring S renaming (zero to *-zero)
open EqR setoid

open import Algebra.Operations.CommutativeMonoid +-commutativeMonoid public

------------------------------------------------------------------------
-- Operations

-- Exponentiation.

infixr 8 _^_

_^_ : Carrier → ℕ → Carrier
x ^ zero  = 1#
x ^ suc n = x * x ^ n

------------------------------------------------------------------------
-- Some properties

-- _× 1# is homomorphic with respect to _ℕ*_/_*_.

×1-homo-* : ∀ m n → (m ℕ* n) × 1# ≈ (m × 1#) * (n × 1#)
×1-homo-* 0 n = begin
  0#             ≈⟨ sym $ Σ.proj₁ *-zero (n × 1#) ⟩
  0# * (n × 1#)  ∎
×1-homo-* (suc m) n = begin
  (n ℕ+ m ℕ* n) × 1#                   ≈⟨ ×-homo-+ 1# n (m ℕ* n) ⟩
  n × 1# + (m ℕ* n) × 1#               ≈⟨ +-cong refl (×1-homo-* m n) ⟩
  n × 1# + (m × 1#) * (n × 1#)         ≈⟨ sym $ +-cong (*-identityˡ (n × 1#)) refl ⟩
  1# * (n × 1#) + (m × 1#) * (n × 1#)  ≈⟨ sym $ distribʳ (n × 1#) 1# (m × 1#) ⟩
  (1# + m × 1#) * (n × 1#)             ∎

-- _×′ 1# is homomorphic with respect to _ℕ*_/_*_.

×′1-homo-* : ∀ m n → (m ℕ* n) ×′ 1# ≈ (m ×′ 1#) * (n ×′ 1#)
×′1-homo-* m n = begin
  (m ℕ* n) ×′ 1#         ≈⟨ sym $ ×≈×′ (m ℕ* n) 1# ⟩
  (m ℕ* n) ×  1#         ≈⟨ ×1-homo-* m n ⟩
  (m ×  1#) * (n ×  1#)  ≈⟨ *-cong (×≈×′ m 1#) (×≈×′ n 1#) ⟩
  (m ×′ 1#) * (n ×′ 1#)  ∎

-- _^_ preserves equality.

^-cong : _^_ Preserves₂ _≈_ ⟶ _≡_ ⟶ _≈_
^-cong {x} {x'} {n} {n'} x≈x' n≡n' = begin
  x  ^ n   ≈⟨ reflexive $ PropEq.cong (_^_ x) n≡n' ⟩
  x  ^ n'  ≈⟨ ^-congˡ n' x≈x' ⟩
  x' ^ n'  ∎
  where
  ^-congˡ : ∀ n → (_^ n) Preserves _≈_ ⟶ _≈_
  ^-congˡ zero    x≈x' = refl
  ^-congˡ (suc n) x≈x' = x≈x' ⟨ *-cong ⟩ ^-congˡ n x≈x'
