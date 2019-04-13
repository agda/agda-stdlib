------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of unique lists (setoid equality)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.Unique.Setoid.Properties where

open import Data.Fin using (Fin)
open import Data.List
open import Data.List.Relation.Binary.Disjoint.Setoid
open import Data.List.Relation.Binary.Disjoint.Setoid.Properties
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Unique.Setoid
import Data.List.Relation.Unary.AllPairs.Properties as AllPairs
open import Data.Nat
open import Function using (_∘_)
open import Relation.Binary using (Rel; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contraposition)

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for list operations
------------------------------------------------------------------------
-- map

module _ {a b ℓ₁ ℓ₂} (S : Setoid a ℓ₁) (R : Setoid b ℓ₂) where

  open Setoid S renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid R renaming (Carrier to B; _≈_ to _≈₂_)

  map⁺ : ∀ {f} → (∀ {x y} → f x ≈₂ f y → x ≈₁ y) →
         ∀ {xs} → Unique S xs → Unique R (map f xs)
  map⁺ inj xs! = AllPairs.map⁺ (AllPairs.map (contraposition inj) xs!)

------------------------------------------------------------------------
-- ++

module _ {a ℓ} (S : Setoid a ℓ) where

  ++⁺ : ∀ {xs ys} → Unique S xs → Unique S ys → Disjoint S xs ys → Unique S (xs ++ ys)
  ++⁺ xs! ys! xs#ys = AllPairs.++⁺ xs! ys! (Disjoint⇒AllAll S xs#ys)

------------------------------------------------------------------------
-- concat

module _ {a ℓ} (S : Setoid a ℓ) where

  concat⁺ : ∀ {xss} → All (Unique S) xss → AllPairs (Disjoint S) xss → Unique S (concat xss)
  concat⁺ xss! xss# = AllPairs.concat⁺ xss! (AllPairs.map (Disjoint⇒AllAll S) xss#)

------------------------------------------------------------------------
-- take & drop

module _ {a ℓ} (S : Setoid a ℓ) where

  drop⁺ : ∀ {xs} n → Unique S xs → Unique S (drop n xs)
  drop⁺ = AllPairs.drop⁺

  take⁺ : ∀ {xs} n → Unique S xs → Unique S (take n xs)
  take⁺ = AllPairs.take⁺

------------------------------------------------------------------------
-- applyUpTo

module _ {a ℓ} (S : Setoid a ℓ) where

  open Setoid S using (_≈_) renaming (Carrier to A)
  private
    _≉_ : Rel A ℓ
    x ≉ y = ¬ (x ≈ y)

  applyUpTo⁺₁ : ∀ f n → (∀ {i j} → i < j → j < n → f i ≉ f j) →
                Unique S (applyUpTo f n)
  applyUpTo⁺₁ = AllPairs.applyUpTo⁺₁

  applyUpTo⁺₂ : ∀ f n → (∀ i j → f i ≉ f j) →
                Unique S (applyUpTo f n)
  applyUpTo⁺₂ = AllPairs.applyUpTo⁺₂

------------------------------------------------------------------------
-- applyDownFrom

module _ {a ℓ} (S : Setoid a ℓ) where

  open Setoid S using (_≈_) renaming (Carrier to A)
  private
    _≉_ : Rel A ℓ
    x ≉ y = ¬ (x ≈ y)

  applyDownFrom⁺₁ : ∀ f n → (∀ {i j} → j < i → i < n → f i ≉ f j) →
                    Unique S (applyDownFrom f n)
  applyDownFrom⁺₁ = AllPairs.applyDownFrom⁺₁

  applyDownFrom⁺₂ : ∀ f n → (∀ i j → f i ≉ f j) →
                    Unique S (applyDownFrom f n)
  applyDownFrom⁺₂ = AllPairs.applyDownFrom⁺₂

------------------------------------------------------------------------
-- tabulate

module _ {a ℓ} (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)

  tabulate⁺ : ∀ {n} {f : Fin n → A} → (∀ {i j} → f i ≈ f j → i ≡ j) →
              Unique S (tabulate f)
  tabulate⁺ f-inj = AllPairs.tabulate⁺ (_∘ f-inj)

------------------------------------------------------------------------
-- filter

module _ {a ℓ} (S : Setoid a ℓ) {p} {P : Pred _ p} (P? : Decidable P) where

  open Setoid S renaming (Carrier to A)

  filter⁺ : ∀ {xs} → Unique S xs → Unique S (filter P? xs)
  filter⁺ = AllPairs.filter⁺ P?
