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
open import Data.Vec.Functional using (Vector)
open import Data.Vec.Functional.Relation.Binary.Permutation using (_↭_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open import Relation.Binary.Indexed.Heterogeneous
  using (Reflexive; Symmetric; Transitive; IsIndexedEquivalence; IndexedSetoid)

private
  variable
    a : Level
    A : Set a
    n : ℕ
    xs ys : Vector A n


------------------------------------------------------------------------
-- Basics

↭-refl : Reflexive (Vector A) _↭_
↭-refl = id , λ _ → refl

↭-reflexive : xs ≡ ys → xs ↭ ys
↭-reflexive refl = ↭-refl

↭-sym : Symmetric (Vector A) _↭_
proj₁ (↭-sym (xs↭ys , _)) = flip xs↭ys
proj₂ (↭-sym {x = xs} {ys} (xs↭ys , xs↭ys≡)) i = begin
  ys (flip xs↭ys ⟨$⟩ʳ i)              ≡⟨ xs↭ys≡ _ ⟨
  xs (xs↭ys ⟨$⟩ʳ (flip xs↭ys ⟨$⟩ʳ i)) ≡⟨ cong xs (inverseʳ xs↭ys) ⟩
  xs i                                ∎
  where open ≡-Reasoning

↭-trans : Transitive (Vector A) _↭_
proj₁ (↭-trans (xs↭ys , _) (ys↭zs , _))   = ys↭zs ∘ₚ xs↭ys
proj₂ (↭-trans (_ , xs↭ys) (_ , ys↭zs)) _ = trans (xs↭ys _) (ys↭zs _)

------------------------------------------------------------------------
-- Structure

isIndexedEquivalence : IsIndexedEquivalence (Vector A) _↭_
isIndexedEquivalence {A = A} = record
  { refl = ↭-refl
  ; sym = ↭-sym
  ; trans = λ {n₁ n₂ n₃} {xs : Vector A n₁} {ys : Vector A n₂} {zs : Vector A n₃}
              xs↭ys ys↭zs → ↭-trans {i = n₁} {i = xs} xs↭ys ys↭zs
  }

------------------------------------------------------------------------
-- Bundle

indexedSetoid : {A : Set a} → IndexedSetoid ℕ a _
indexedSetoid {A = A} = record
  { Carrier = Vector A
  ; _≈_ = _↭_
  ; isEquivalence = isIndexedEquivalence
  }
