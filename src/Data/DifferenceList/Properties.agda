------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on DiffList
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.DifferenceList.Properties where

open import Data.DifferenceList.Base
  using (DiffList; fromList; toList; []; _∷_; [_]; _++_; _∷ʳ_; map)
open import Data.List as List using (List)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Function using (id)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; _≗_; module ≡-Reasoning)

open ≡-Reasoning

private
  variable
    a b : Level
    A : Set a
    B : Set b
    xs xs₁ xs₂ : List A
    ys ys₁ ys₂ : DiffList A


------------------------------------------------------------------------
-- Relation between Lists and equivalent DiffLists

infix 4 _∼_
_∼_ : List A → DiffList A → Set _
xs ∼ ys = fromList xs ≗ ys

------------------------------------------------------------------------
-- Properties of fromList and toList

∼-fromList : xs ∼ fromList xs
∼-fromList _ = refl

toList∘fromList : (xs : List A) → toList (fromList xs) ≡ xs
toList∘fromList = ++-identityʳ

toList⁺ : xs ∼ ys → xs ≡ toList ys
toList⁺ {xs = xs} {ys} xs∼ys = begin
  xs                  ≡⟨ (++-identityʳ xs) ⟨
  xs List.++ List.[]  ≡⟨ xs∼ys List.[] ⟩
  ys List.[]          ≡⟨⟩
  toList ys           ∎

------------------------------------------------------------------------
-- Properties of operations that preserve _∼_

[]⁺ : List.[] {A = A} ∼ []
[]⁺ _ = refl

[_]⁺ : (x : A) → List.[ x ] ∼ [ x ]
[_]⁺ _ _ = refl

++⁺ : xs₁ ∼ ys₁ → xs₂ ∼ ys₂ → xs₁ List.++ xs₂ ∼ ys₁ ++ ys₂
++⁺ {xs₁ = xs₁} {ys₁ = ys₁} {xs₂ = xs₂} {ys₂ = ys₂}
    xs₁∼ys₁ xs₂∼ys₂ k = begin
  (xs₁ List.++ xs₂) List.++ k  ≡⟨ ++-assoc xs₁ xs₂ k ⟩
  xs₁ List.++ (xs₂ List.++ k)  ≡⟨ cong (xs₁ List.++_) (xs₂∼ys₂ k) ⟩
  xs₁ List.++ ys₂ k            ≡⟨ xs₁∼ys₁ (ys₂ k) ⟩
  ys₁ (ys₂ k)                  ≡⟨⟩
  (ys₁ ++ ys₂) k               ∎

∷⁺ : (x : A) → xs ∼ ys → x List.∷ xs ∼ x ∷ ys
∷⁺ {xs = xs} {ys} x xs~ys k = cong (x List.∷_) (xs~ys k)

++-∷⁺ : (x : A) → xs₁ ∼ ys₁ → xs₂ ∼ ys₂ →
        xs₁ List.++ x List.∷ xs₂ ∼ ys₁ ++ x ∷ ys₂
++-∷⁺ x xs₁∼ys₁ xs₂∼ys₂ = ++⁺ xs₁∼ys₁ (∷⁺ x xs₂∼ys₂)

∷ʳ⁺ : (x : A) → xs ∼ ys → xs List.∷ʳ x ∼ ys ∷ʳ x
∷ʳ⁺ {xs = xs} {ys} x xs∼ys k = ++⁺ xs∼ys [ x ]⁺ k

map⁺ : (f : A → B) → xs ∼ ys → List.map f xs ∼ map f ys
map⁺ f xs∼ys k =
  cong (λ xs → fromList (List.map f xs) k) (toList⁺ xs∼ys)
