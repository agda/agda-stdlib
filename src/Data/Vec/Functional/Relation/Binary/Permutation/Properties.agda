------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of permutation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Functional.Relation.Binary.Permutation.Properties where

open import Level using (Level)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Nat using (ℕ)
open import Data.Fin.Permutation using (id; flip; _⟨$⟩ʳ_; inverseʳ; _∘ₚ_)
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Permutation
open import Relation.Binary.PropositionalEquality
  using (refl; trans; _≡_; cong; module ≡-Reasoning)

open ≡-Reasoning

private
  variable
    ℓ : Level
    A : Set ℓ
    n : ℕ
    xs ys zs : Vector A n

↭-refl : xs ↭ xs
↭-refl = id , λ _ → refl

↭-reflexive : xs ≡ ys → xs ↭ ys
↭-reflexive refl = ↭-refl

↭-sym : xs ↭ ys → ys ↭ xs
proj₁ (↭-sym (xs↭ys , _)) = flip xs↭ys
proj₂ (↭-sym {xs = xs} {ys = ys} (xs↭ys , xs↭ys≡)) i = begin
  ys (flip xs↭ys ⟨$⟩ʳ i)             ≡˘⟨ xs↭ys≡ _ ⟩
  xs (xs↭ys ⟨$⟩ʳ (flip xs↭ys ⟨$⟩ʳ i)) ≡⟨ cong xs (inverseʳ xs↭ys) ⟩
  xs i ∎

↭-trans : xs ↭ ys → ys ↭ zs → xs ↭ zs
proj₁ (↭-trans (xs↭ys , _) (ys↭zs , _))   = ys↭zs ∘ₚ xs↭ys
proj₂ (↭-trans (_ , xs↭ys) (_ , ys↭zs)) _ = trans (xs↭ys _) (ys↭zs _)
