------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural numbers: properties of sum and product
--
-- Issue #2553: this is a compatibility stub module,
-- ahead of a more thorough breaking set of changes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.ListAction.Properties where

open import Algebra.Bundles using (CommutativeMonoid)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭⇒↭ₛ)
open import Data.List.Relation.Binary.Permutation.Setoid.Properties
  using (foldr-commMonoid)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ; _+_; _*_; NonZero; _≤_)
open import Data.Nat.Divisibility using (_∣_; m∣m*n; ∣n⇒∣m*n)
open import Data.Nat.ListAction using (sum; product)
open import Data.Nat.Properties
  using (+-assoc; *-assoc; *-identityˡ; m*n≢0; m≤m*n; m≤n⇒m≤o*n
        ; +-0-commutativeMonoid; *-1-commutativeMonoid)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)

private
  variable
    m n : ℕ
    ms ns : List ℕ


------------------------------------------------------------------------
-- Properties

-- sum

sum-++ : ∀ ms ns → sum (ms ++ ns) ≡ sum ms + sum ns
sum-++ []       ns = refl
sum-++ (m ∷ ms) ns = begin
  m + sum (ms ++ ns)     ≡⟨ cong (m +_) (sum-++ ms ns) ⟩
  m + (sum ms + sum ns)  ≡⟨ +-assoc m _ _ ⟨
  (m + sum ms) + sum ns  ∎
  where open ≡-Reasoning

sum-↭ : sum Preserves _↭_ ⟶ _≡_
sum-↭ p = foldr-commMonoid ℕ-+-0.setoid ℕ-+-0.isCommutativeMonoid (↭⇒↭ₛ p)
  where module ℕ-+-0 = CommutativeMonoid +-0-commutativeMonoid


-- product

product-++ : ∀ ms ns → product (ms ++ ns) ≡ product ms * product ns
product-++ []       ns = sym (*-identityˡ _)
product-++ (m ∷ ms) ns = begin
  m * product (ms ++ ns)         ≡⟨ cong (m *_) (product-++ ms ns) ⟩
  m * (product ms * product ns)  ≡⟨ *-assoc m _ _ ⟨
  (m * product ms) * product ns  ∎
  where open ≡-Reasoning

∈⇒∣product : n ∈ ns → n ∣ product ns
∈⇒∣product {ns = n ∷ ns} (here  refl) = m∣m*n (product ns)
∈⇒∣product {ns = m ∷ ns} (there n∈ns) = ∣n⇒∣m*n m (∈⇒∣product n∈ns)

product≢0 : All NonZero ns → NonZero (product ns)
product≢0 []           = _
product≢0 (n≢0 ∷ ns≢0) = m*n≢0 _ _ {{n≢0}} {{product≢0 ns≢0}}

∈⇒≤product : All NonZero ns → n ∈ ns → n ≤ product ns
∈⇒≤product (n≢0 ∷ ns≢0) (here refl)  = m≤m*n _ _ {{product≢0 ns≢0}}
∈⇒≤product (n≢0 ∷ ns≢0) (there n∈ns) = m≤n⇒m≤o*n _ {{n≢0}} (∈⇒≤product ns≢0 n∈ns)

product-↭ : product Preserves _↭_ ⟶ _≡_
product-↭ p = foldr-commMonoid ℕ-*-1.setoid ℕ-*-1.isCommutativeMonoid (↭⇒↭ₛ p)
  where module ℕ-*-1 = CommutativeMonoid *-1-commutativeMonoid
