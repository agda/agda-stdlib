------------------------------------------------------------------------
-- The Agda standard library
--
-- Sorted lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.Sorted.TotalOrder.Properties where

open import Data.List.Base
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Linked as Linked
  using (Linked; []; [-]; _∷_; _∷′_; head′; tail)
import Data.List.Relation.Unary.Linked.Properties as Linked
open import Data.List.Relation.Unary.Sorted.TotalOrder hiding (head)
open import Data.Maybe.Base using (just; nothing)
open import Data.Maybe.Relation.Binary.Connected using (Connected; just)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; z≤n; s≤s)
open import Level using (Level)
open import Relation.Binary hiding (Decidable)
import Relation.Binary.Properties.TotalOrder as TotalOrderProperties
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (yes; no)
private
  variable
    a b p ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

------------------------------------------------------------------------
-- Relationship to other predicates
------------------------------------------------------------------------

module _ (O : TotalOrder a ℓ₁ ℓ₂) where
  open TotalOrder O

  AllPairs⇒Sorted : ∀ {xs} → AllPairs _≤_ xs → Sorted O xs
  AllPairs⇒Sorted = Linked.AllPairs⇒Linked

  Sorted⇒AllPairs : ∀ {xs} → Sorted O xs → AllPairs _≤_ xs
  Sorted⇒AllPairs = Linked.Linked⇒AllPairs trans

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for list operations
------------------------------------------------------------------------
-- map

module _ (O₁ : TotalOrder a ℓ₁ ℓ₂) (O₂ : TotalOrder a ℓ₁ ℓ₂) where
  private
    module O₁ = TotalOrder O₁
    module O₂ = TotalOrder O₂

  map⁺ : ∀ {f xs} → f Preserves O₁._≤_ ⟶ O₂._≤_ →
         Sorted O₁ xs → Sorted O₂ (map f xs)
  map⁺ pres xs↗ = Linked.map⁺ (Linked.map pres xs↗)

  map⁻ : ∀ {f xs} → (∀ {x y} → f x O₂.≤ f y → x O₁.≤ y) →
         Sorted O₂ (map f xs) → Sorted O₁ xs
  map⁻ pres fxs↗ = Linked.map pres (Linked.map⁻ fxs↗)

------------------------------------------------------------------------
-- _++_

module _ (O : TotalOrder a ℓ₁ ℓ₂) where
  open TotalOrder O

  ++⁺ : ∀ {xs ys} → Sorted O xs → Connected _≤_ (last xs) (head ys) →
        Sorted O ys → Sorted O (xs ++ ys)
  ++⁺ = Linked.++⁺

------------------------------------------------------------------------
-- applyUpTo

module _ (O : TotalOrder a ℓ₁ ℓ₂) where
  open TotalOrder O

  applyUpTo⁺₁ : ∀ f n → (∀ {i} → suc i < n → f i ≤ f (suc i)) →
                Sorted O (applyUpTo f n)
  applyUpTo⁺₁ = Linked.applyUpTo⁺₁

  applyUpTo⁺₂ : ∀ f n → (∀ i → f i ≤ f (suc i)) →
                Sorted O (applyUpTo f n)
  applyUpTo⁺₂ = Linked.applyUpTo⁺₂

------------------------------------------------------------------------
-- applyDownFrom

module _ (O : TotalOrder a ℓ₁ ℓ₂) where
  open TotalOrder O

  applyDownFrom⁺₁ : ∀ f n → (∀ {i} → suc i < n → f (suc i) ≤ f i) →
                    Sorted O (applyDownFrom f n)
  applyDownFrom⁺₁ = Linked.applyDownFrom⁺₁

  applyDownFrom⁺₂ : ∀ f n → (∀ i → f (suc i) ≤ f i) →
                    Sorted O (applyDownFrom f n)
  applyDownFrom⁺₂ = Linked.applyDownFrom⁺₂


------------------------------------------------------------------------
-- merge

module _ (DO : DecTotalOrder a ℓ₁ ℓ₂) where
  open DecTotalOrder DO renaming (totalOrder to O)
  open TotalOrderProperties O using (≰⇒≥)

  private
    merge-con : ∀ {v xs ys} →
                Connected _≤_ (just v) (head xs) →
                Connected _≤_ (just v) (head ys) →
                Connected _≤_ (just v) (head (merge _≤?_ xs ys))
    merge-con {xs = []}     {[]}     cxs cys = cys
    merge-con {xs = []}     {y ∷ ys} cxs cys = cys
    merge-con {xs = x ∷ xs} {[]}     cxs cys = cxs
    merge-con {xs = x ∷ xs} {y ∷ ys} cxs cys with x ≤? y
    ... | yes x≤y = cxs
    ... | no  x≰y = cys

  merge⁺ : ∀ {xs ys} → Sorted O xs → Sorted O ys → Sorted O (merge _≤?_ xs ys)
  merge⁺ {[]}     {[]}     rxs rys = []
  merge⁺ {[]}     {x ∷ ys} rxs rys = rys
  merge⁺ {x ∷ xs} {[]}     rxs rys = rxs
  merge⁺ {x ∷ xs} {y ∷ ys} rxs rys with x ≤? y |
    merge⁺ (Linked.tail rxs) rys | merge⁺ rxs (Linked.tail rys)
  ... | yes x≤y | rec | _   = merge-con (head′ rxs)      (just x≤y)  ∷′ rec
  ... | no  x≰y | _   | rec = merge-con (just (≰⇒≥ x≰y)) (head′ rys) ∷′ rec

------------------------------------------------------------------------
-- filter

module _ (O : TotalOrder a ℓ₁ ℓ₂) {P : Pred _ p} (P? : Decidable P) where
  open TotalOrder O

  filter⁺ : ∀ {xs} → Sorted O xs → Sorted O (filter P? xs)
  filter⁺ = Linked.filter⁺ P? trans
