------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on DiffList
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.DifferenceList.Properties where

open import Data.DifferenceList.Base
  using (DiffList; fromList; toList; viaList; []; _∷_; [_]; _++_; _∷ʳ_; map)
open import Data.List.Base as List using (List)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Product using (Σ; _,_)
open import Function.Base using (_∘′_; id; flip)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; cong; _≗_; module ≡-Reasoning)

open ≡-Reasoning

private
  variable
    a b : Level
    A : Set a
    B : Set b
    xs ys : List A
    dxs dys : DiffList A


------------------------------------------------------------------------
-- Relation between Lists and equivalent DiffLists

infix 4 _∼_
_∼_ : List A → DiffList A → Set _
xs ∼ dxs = fromList xs ≗ dxs

ListLike : DiffList A → Set _
ListLike {A = A} dxs = Σ (List A) (_∼ dxs)

------------------------------------------------------------------------
-- Properties of fromList and toList

∼-fromList : xs ∼ fromList xs
∼-fromList _ = refl

toList∘fromList : (xs : List A) → toList (fromList xs) ≡ xs
toList∘fromList = ++-identityʳ

toList⁺ : xs ∼ dxs → xs ≡ toList dxs
toList⁺ {xs = xs} {dxs} x∼ = begin
  xs                  ≡⟨ ++-identityʳ xs ⟨
  xs List.++ List.[]  ≡⟨ x∼ List.[] ⟩
  dxs List.[]         ≡⟨⟩
  toList dxs          ∎

toList-++ : ListLike dxs → (dys : DiffList A) →
            toList dxs List.++ toList dys ≡ toList (dxs ++ dys)
toList-++ {dxs = dxs} (xs , x∼) dys = begin
  toList dxs List.++ toList dys  ≡⟨ cong (List._++ toList dys) (toList⁺ x∼) ⟨
  xs List.++ toList dys          ≡⟨⟩
  fromList xs (toList dys)       ≡⟨ x∼ (toList dys) ⟩
  dxs (toList dys)               ≡⟨⟩
  toList (dxs ++ dys)            ∎

viaList⁺ : (f : List A → List B) → xs ∼ dxs → f xs ∼ viaList f dxs
viaList⁺ {xs = xs} {dxs = dxs} f x∼ k = begin
  fromList (f xs)           k  ≡⟨ cong (flip fromList _ ∘′ f) (toList⁺ x∼) ⟩
  fromList (f (toList dxs)) k  ≡⟨⟩
  viaList f dxs             k  ∎

------------------------------------------------------------------------
-- Properties of operations that preserve _∼_

[]⁺ : List.[] {A = A} ∼ []
[]⁺ _ = refl

[_]⁺ : (x : A) → List.[ x ] ∼ [ x ]
[_]⁺ _ _ = refl

++⁺ : xs ∼ dxs → ys ∼ dys → xs List.++ ys ∼ dxs ++ dys
++⁺ {xs = xs} {dxs = dxs} {ys = ys} {dys = dys} x∼ y∼ k = begin
  (xs List.++ ys) List.++ k  ≡⟨ ++-assoc xs ys k ⟩
  xs List.++ (ys List.++ k)  ≡⟨ cong (xs List.++_) (y∼ k) ⟩
  xs List.++ dys k           ≡⟨ x∼ (dys k) ⟩
  dxs (dys k)                ≡⟨⟩
  (dxs ++ dys) k             ∎

∷⁺ : (x : A) → xs ∼ dxs → x List.∷ xs ∼ x ∷ dxs
∷⁺ x x∼ k = cong (x List.∷_) (x∼ k)

∷ʳ⁺ : (x : A) → xs ∼ dxs → xs List.∷ʳ x ∼ dxs ∷ʳ x
∷ʳ⁺ x x∼ k = ++⁺ x∼ [ x ]⁺ k

map⁺ : (f : A → B) → xs ∼ dxs → List.map f xs ∼ map f dxs
map⁺ f = viaList⁺ _
