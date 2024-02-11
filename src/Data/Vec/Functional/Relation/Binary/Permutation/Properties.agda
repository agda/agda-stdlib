------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of permutation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Functional.Relation.Binary.Permutation.Properties where

open import Level using (Level)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Permutation using (id; flip; _⟨$⟩ʳ_; inverseʳ; _∘ₚ_)
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Permutation
open import Relation.Binary.PropositionalEquality
  using (refl; trans; _≡_; cong; module ≡-Reasoning)
open import Relation.Binary.Indexed.Heterogeneous.Definitions

open ≡-Reasoning

private
  variable
    ℓ : Level
    A : Set ℓ
    n : ℕ
    xs ys zs : Vector A n

↭-refl : Reflexive (Vector A) _↭_
↭-refl = id , λ _ → refl

↭-reflexive : xs ≡ ys → xs ↭ ys
↭-reflexive refl = ↭-refl

↭-sym : Symmetric (Vector A) _↭_
proj₁ (↭-sym (xs↭ys , _)) = flip xs↭ys
proj₂ (↭-sym {x = xs} {ys} (xs↭ys , xs↭ys≡)) i = begin
  ys (flip xs↭ys ⟨$⟩ʳ i)             ≡˘⟨ xs↭ys≡ _ ⟩
  xs (xs↭ys ⟨$⟩ʳ (flip xs↭ys ⟨$⟩ʳ i)) ≡⟨ cong xs (inverseʳ xs↭ys) ⟩
  xs i ∎

↭-trans : Transitive (Vector A) _↭_
proj₁ (↭-trans (xs↭ys , _) (ys↭zs , _))   = ys↭zs ∘ₚ xs↭ys
proj₂ (↭-trans (_ , xs↭ys) (_ , ys↭zs)) _ = trans (xs↭ys _) (ys↭zs _)
