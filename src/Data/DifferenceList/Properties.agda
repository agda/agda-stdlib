------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on DiffList
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.DifferenceList.Properties where

open import Data.DifferenceList.Base
  using (DiffList; fromList; toList; lift; []; _∷_; [_]; _++_; _∷ʳ_; map)
open import Data.List as List using (List)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Function using (id)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; module ≡-Reasoning)

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
_∼_ : {A : Set a} → List A → DiffList A → Set a
_∼_ {A = A} xs ys = (k : List A) → fromList xs k ≡ ys k

------------------------------------------------------------------------
-- Properties of fromList and toList

∼-fromList : xs ∼ fromList xs
∼-fromList _ = refl

toList∘fromList : (xs : List A) → toList (fromList xs) ≡ xs
toList∘fromList = ++-identityʳ

toList⁺ : xs ∼ ys → xs ≡ toList ys
toList⁺ {xs = xs} {ys} xs∼ys = begin
  xs                  ≡⟨ sym (++-identityʳ xs) ⟩
  xs List.++ List.[]  ≡⟨ xs∼ys List.[] ⟩
  ys List.[]          ≡⟨⟩
  toList ys           ∎

fromList⁺ : xs ∼ ys → (k : List A) → fromList xs k ≡ ys k
fromList⁺ = id

------------------------------------------------------------------------
-- Properties of operations that preserve _∼_

-- `lift` preserves `∼` when `f` is a prepend
lift⁺ : (f : List A → List A) →
        (∀ xs′ → f xs′ ≡ f List.[] List.++ xs′) →
        xs ∼ ys → f xs ∼ lift f ys
lift⁺ {xs = xs} {ys = ys} f prepend xs∼ys k = begin
  f xs List.++ k                    ≡⟨ cong (List._++ k) (prepend xs) ⟩
  (f List.[] List.++ xs) List.++ k  ≡⟨ ++-assoc (f List.[]) xs k ⟩
  f List.[] List.++ (xs List.++ k)  ≡⟨ sym (prepend (xs List.++ k)) ⟩
  f (xs List.++ k)                  ≡⟨ cong f (xs∼ys k) ⟩
  f (ys k)                          ≡⟨⟩
  lift f ys k                       ∎

[]⁺ : List.[] {A = A} ∼ []
[]⁺ _ = refl

∷⁺ : (x : A) → xs ∼ ys → x List.∷ xs ∼ x ∷ ys
∷⁺ x = lift⁺ (x List.∷_) (λ _ → refl)

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

++-∷⁺ : (x : A) → xs₁ ∼ ys₁ → xs₂ ∼ ys₂ →
        xs₁ List.++ x List.∷ xs₂ ∼ ys₁ ++ x ∷ ys₂
++-∷⁺ x xs₁∼ys₁ xs₂∼ys₂ = ++⁺ xs₁∼ys₁ (∷⁺ x xs₂∼ys₂)

∷ʳ⁺ : (x : A) → xs ∼ ys → xs List.∷ʳ x ∼ ys ∷ʳ x
∷ʳ⁺ {xs = xs} {ys} x xs∼ys k = begin
  xs List.∷ʳ x List.++ k             ≡⟨⟩
  (xs List.++ List.[ x ]) List.++ k  ≡⟨ ++-assoc xs List.[ x ] k ⟩
  xs List.++ (x List.∷ k)            ≡⟨ xs∼ys (x List.∷ k) ⟩
  ys (x List.∷ k)                    ≡⟨⟩
  (ys ∷ʳ x) k                        ∎

map⁺ : (f : A → B) → xs ∼ ys → List.map f xs ∼ map f ys
map⁺ f xs∼ys k =
  cong (λ xs → fromList (List.map f xs) k) (toList⁺ xs∼ys)
