------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of unique vectors (setoid equality)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Relation.Unary.Unique.Setoid.Properties where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Vec.Base as Vec
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
import Data.Vec.Relation.Unary.All.Properties as All
open import Data.Vec.Relation.Unary.AllPairs as AllPairs using (AllPairs)
open import Data.Vec.Relation.Unary.Unique.Setoid
import Data.Vec.Relation.Unary.AllPairs.Properties as AllPairs
open import Data.Nat.Base using (ℕ; _+_)
open import Function.Base using (_∘_; id)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Nullary.Negation using (contradiction; contraposition)

private
  variable
    a b c p ℓ ℓ₁ ℓ₂ ℓ₃ : Level

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for list operations
------------------------------------------------------------------------
-- map

module _ (S : Setoid a ℓ₁) (R : Setoid b ℓ₂) where

  open Setoid S renaming (_≈_ to _≈₁_)
  open Setoid R renaming (_≈_ to _≈₂_)

  map⁺ : ∀ {f} → (∀ {x y} → f x ≈₂ f y → x ≈₁ y) →
         ∀ {n xs} → Unique S {n} xs → Unique R {n} (map f xs)
  map⁺ inj xs! = AllPairs.map⁺ (AllPairs.map (contraposition inj) xs!)

------------------------------------------------------------------------
-- take & drop

module _ (S : Setoid a ℓ) where

  drop⁺ : ∀ {n} m {xs} → Unique S {m + n} xs → Unique S {n} (drop m xs)
  drop⁺ = AllPairs.drop⁺

  take⁺ : ∀ {n} m {xs} → Unique S {m + n} xs → Unique S {m} (take m xs)
  take⁺ = AllPairs.take⁺

------------------------------------------------------------------------
-- tabulate

module _ (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)

  tabulate⁺ : ∀ {n} {f : Fin n → A} → (∀ {i j} → f i ≈ f j → i ≡ j) →
              Unique S (tabulate f)
  tabulate⁺ f-inj = AllPairs.tabulate⁺ (_∘ f-inj)

------------------------------------------------------------------------
-- lookup

module _ (S : Setoid a ℓ) where

  open Setoid S

  lookup-injective : ∀ {n xs} → Unique S {n} xs → ∀ i j → lookup xs i ≈ lookup xs j → i ≡ j
  lookup-injective (px ∷ pxs) zero zero eq = ≡.refl
  lookup-injective (px ∷ pxs) zero (suc j) eq = contradiction eq (All.lookup⁺ px j)
  lookup-injective (px ∷ pxs) (suc i) zero eq = contradiction (sym eq) (All.lookup⁺ px i)
  lookup-injective (px ∷ pxs) (suc i) (suc j) eq = ≡.cong suc (lookup-injective pxs i j eq)
