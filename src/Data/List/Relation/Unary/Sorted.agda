------------------------------------------------------------------------
-- The Agda standard library
--
-- Inductive pointwise sorting of vectors
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.Sorted where

open import Data.Nat using (suc; _≤_; _<_; z≤n; s≤s; ⌈_/2⌉; ⌊_/2⌋)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe as M using (Maybe; nothing; just)
open import Data.Unit using (⊤; tt)
open import Data.Product as Σ using (Σ; Σ-syntax; _×_; _,_; uncurry; proj₁; proj₂)
open import Data.Sum as ⊎ using (_⊎_; inj₁; inj₂)
open import Relation.Binary as B using (Rel; Total)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Unary as U using (Pred)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Induction.WellFounded using (Acc; acc)
open import Level using (_⊔_; Lift; lift) renaming (suc to lsuc)

Sorted-≺-head : ∀ {a ℓ} {A : Set a} → Rel A ℓ → A → List A → Set ℓ
Sorted-≺-head _≺_ x [] = Lift _ ⊤
Sorted-≺-head _≺_ x (y ∷ xs) = x ≺ y

data Sorted {a ℓ} {A : Set a} (_≺_ : Rel A ℓ) : Pred (List A) (a ⊔ ℓ) where
  [] : Sorted _≺_ []
  _∷_ : ∀ {x xs} → Sorted-≺-head _≺_ x xs → Sorted _≺_ xs → Sorted _≺_ (x ∷ xs)

Monotonic : ∀ {a ℓ} {A : Set a} → (_≺_ : Rel A ℓ) → Pred (List A) (a ⊔ ℓ)
Monotonic _≺_ = AllPairs _≺_

module _ {a ℓ} {A : Set a} {_≺_ : Rel A ℓ} where
  private
    Sort = Sorted _≺_
    _≺-head_ = Sorted-≺-head _≺_

  sorted : B.Decidable _≺_ → U.Decidable Sort
  sorted _≺?_ [] = yes []
  sorted _≺?_ (x ∷ []) = yes (lift tt ∷ [])
  sorted _≺?_ (x ∷ y ∷ xs) = Dec.map′ (uncurry _∷_) (λ {(x≺y ∷ sort[y∷xs]) → x≺y , sort[y∷xs]}) (x ≺? y ×-dec sorted _≺?_ (y ∷ xs)) where

  module _ (≺-total : Total _≺_) where
    module Merge where
      mutual
        -- Split into 2 helper functions to make termination checker happy
        merge-auxₗ : A → List A → List A → List A
        merge-auxₗ x xs [] = x ∷ xs
        merge-auxₗ x xs (y ∷ ys) with ≺-total x y
        merge-auxₗ x xs (y ∷ ys) | inj₁ x≺y = x ∷ merge-auxᵣ xs y ys
        merge-auxₗ x xs (y ∷ ys) | inj₂ y≺x = y ∷ merge-auxₗ x xs ys

        merge-auxᵣ : List A → A → List A → List A
        merge-auxᵣ [] y ys = y ∷ ys
        merge-auxᵣ (x ∷ xs) y ys with ≺-total x y
        merge-auxᵣ (x ∷ xs) y ys | inj₁ x≺y = x ∷ merge-auxᵣ xs y ys
        merge-auxᵣ (x ∷ xs) y ys | inj₂ y≺x = y ∷ merge-auxₗ x xs ys

      merge : List A → List A → List A
      merge [] ys = ys
      merge (x ∷ xs) ys = merge-auxₗ x xs ys

      split : List A → List A × List A
      split [] = [] , []
      split (x ∷ xs) = x ∷ proj₂ r , proj₁ r where
        r = split xs

      split-length : ∀ xs → (let ys = split xs) (let n = length xs) → (length (proj₁ ys) ≡ ⌈ n /2⌉) × (length (proj₂ ys)) ≡ ⌊ n /2⌋
      split-length [] = P.refl , P.refl
      split-length (x ∷ []) = P.refl , P.refl
      split-length (x₁ ∷ x₂ ∷ xs) = Σ.map (P.cong suc) (P.cong suc) (split-length xs)

      split-length₁ : ∀ x₁ x₂ xs → (let ys = split (x₁ ∷ x₂ ∷ xs)) → length (proj₁ ys) < length (x₁ ∷ x₂ ∷ xs)
      split-length₁ x₁ x₂ xs = begin
        1 + length (proj₁ ys)           ≡⟨ P.cong (1 +_) (proj₁ ys-length) ⟩
        1 + ⌈ length (x₁ ∷ x₂ ∷ xs) /2⌉ ≤⟨ ⌈n/2⌉<n (length xs) ⟩
        length (x₁ ∷ x₂ ∷ xs)           ∎
        where
          open import Data.Nat
          open import Data.Nat.Properties
          open ≤-Reasoning
          ys = split (x₁ ∷ x₂ ∷ xs)
          ys-length = split-length (x₁ ∷ x₂ ∷ xs)

      split-length₂ : ∀ x₁ x₂ xs → (let ys = split (x₁ ∷ x₂ ∷ xs)) → length (proj₂ ys) < length (x₁ ∷ x₂ ∷ xs)
      split-length₂ x₁ x₂ xs = begin
        1 + length (proj₂ ys)           ≡⟨ P.cong (1 +_) (proj₂ ys-length) ⟩
        1 + ⌊ length (x₁ ∷ x₂ ∷ xs) /2⌋ ≤⟨ ⌊n/2⌋<n (length (x₂ ∷ xs)) ⟩
        length (x₁ ∷ x₂ ∷ xs)           ∎
        where
          open import Data.Nat
          open import Data.Nat.Properties
          open ≤-Reasoning
          ys = split (x₁ ∷ x₂ ∷ xs)
          ys-length = split-length (x₁ ∷ x₂ ∷ xs)

      merge-sort-aux : (xs : List A) → Acc _<_ (length xs) → List A
      merge-sort-aux [] a = []
      merge-sort-aux (x ∷ []) a = x ∷ []
      merge-sort-aux (x₁ ∷ x₂ ∷ xs) (acc rs) = merge (merge-sort-aux (proj₁ ys) (rs (length (proj₁ ys)) lemma₁)) (merge-sort-aux (proj₂ ys) (rs (length (proj₂ ys)) lemma₂)) where
        ys = split (x₁ ∷ x₂ ∷ xs)
        ys-length = split-length (x₁ ∷ x₂ ∷ xs)
        lemma₁ = split-length₁ x₁ x₂ xs
        lemma₂ = split-length₂ x₁ x₂ xs

      merge-sort : List A → List A
      merge-sort xs = merge-sort-aux xs (<-wellFounded (length xs)) where
        open import Data.Nat.Induction
    open Merge using (merge; merge-sort) public

    module Quick where
      qs-split : A → List A → List A × List A
      qs-split p [] = [] , []
      qs-split p (x ∷ xs) with ≺-total p x
      qs-split p (x ∷ xs) | inj₁ p≺x = Σ.map₂ (x ∷_) (qs-split p xs)
      qs-split p (x ∷ xs) | inj₂ x≺p = Σ.map₁ (x ∷_) (qs-split p xs)

      qs-split-length : ∀ p xs → (let ys = qs-split p xs) → length (proj₁ ys) ≤ length xs × length (proj₂ ys) ≤ length xs
      qs-split-length p [] = z≤n , z≤n
      qs-split-length p (x ∷ xs) with ≺-total p x
      qs-split-length p (x ∷ xs) | inj₁ p≺x = Σ.map ≤-step s≤s (qs-split-length p xs) where open import Data.Nat.Properties
      qs-split-length p (x ∷ xs) | inj₂ x≺p = Σ.map s≤s ≤-step (qs-split-length p xs) where open import Data.Nat.Properties

      qsort-aux : (xs : List A) → Acc _<_ (length xs) → List A
      qsort-aux [] a = []
      qsort-aux (p ∷ xs) (acc rs) = ys₁ ++ p ∷ ys₂ where
        ys = qs-split p xs
        ys-len = qs-split-length p xs
        ys₁ = qsort-aux (proj₁ ys) (rs (length (proj₁ ys)) (s≤s (proj₁ ys-len)))
        ys₂ = qsort-aux (proj₂ ys) (rs (length (proj₂ ys)) (s≤s (proj₂ ys-len)))

      quick-sort : List A → List A
      quick-sort xs = qsort-aux xs (<-wellFounded (length xs)) where
        open import Data.Nat.Induction
    open Quick using (quick-sort)
