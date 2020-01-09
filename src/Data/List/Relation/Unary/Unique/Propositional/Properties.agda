------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of unique lists (setoid equality)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.Unique.Propositional.Properties where

open import Data.Fin using (Fin)
open import Data.List
open import Data.List.Relation.Binary.Disjoint.Propositional
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Unique.Propositional
import Data.List.Relation.Unary.Unique.Setoid.Properties as Setoid
open import Data.Nat
open import Data.Nat.Properties using (<⇒≢)
open import Function using (id; _∘_)
open import Relation.Binary using (Rel; Setoid)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; sym; setoid)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for list operations
------------------------------------------------------------------------
-- map

module _ {a b} {A : Set a} {B : Set b} where

  map⁺ : ∀ {f} → (∀ {x y} → f x ≡ f y → x ≡ y) →
         ∀ {xs} → Unique xs → Unique (map f xs)
  map⁺ = Setoid.map⁺ (setoid A) (setoid B)

------------------------------------------------------------------------
-- ++

module _ {a} {A : Set a} where

  ++⁺ : ∀ {xs ys} → Unique xs → Unique ys → Disjoint xs ys → Unique (xs ++ ys)
  ++⁺ = Setoid.++⁺ (setoid A)

------------------------------------------------------------------------
-- concat

module _ {a} {A : Set a} where

  concat⁺ : ∀ {xss} → All Unique xss → AllPairs Disjoint xss → Unique (concat xss)
  concat⁺ = Setoid.concat⁺ (setoid A)

------------------------------------------------------------------------
-- take & drop

module _ {a} {A : Set a} where

  drop⁺ : ∀ {xs} n → Unique xs → Unique (drop n xs)
  drop⁺ = Setoid.drop⁺ (setoid A)

  take⁺ : ∀ {xs} n → Unique xs → Unique (take n xs)
  take⁺ = Setoid.take⁺ (setoid A)

------------------------------------------------------------------------
-- applyUpTo & upTo

module _ {a} {A : Set a} where

  applyUpTo⁺₁ : ∀ f n → (∀ {i j} → i < j → j < n → f i ≢ f j) →
                Unique (applyUpTo f n)
  applyUpTo⁺₁ = Setoid.applyUpTo⁺₁ (setoid A)

  applyUpTo⁺₂ : ∀ f n → (∀ i j → f i ≢ f j) →
                Unique (applyUpTo f n)
  applyUpTo⁺₂ = Setoid.applyUpTo⁺₂  (setoid A)

------------------------------------------------------------------------
-- upTo

upTo⁺ : ∀ n → Unique (upTo n)
upTo⁺ n = applyUpTo⁺₁ id n (λ i<j _ → <⇒≢ i<j)

------------------------------------------------------------------------
-- applyDownFrom

module _ {a} {A : Set a} where

  applyDownFrom⁺₁ : ∀ f n → (∀ {i j} → j < i → i < n → f i ≢ f j) →
                    Unique (applyDownFrom f n)
  applyDownFrom⁺₁ = Setoid.applyDownFrom⁺₁ (setoid A)

  applyDownFrom⁺₂ : ∀ f n → (∀ i j → f i ≢ f j) →
                    Unique (applyDownFrom f n)
  applyDownFrom⁺₂ = Setoid.applyDownFrom⁺₂ (setoid A)

------------------------------------------------------------------------
-- downFrom

downFrom⁺ : ∀ n → Unique (downFrom n)
downFrom⁺ n = applyDownFrom⁺₁ id n (λ j<i _ → <⇒≢ j<i ∘ sym)

------------------------------------------------------------------------
-- tabulate

module _ {a} {A : Set a} where

  tabulate⁺ : ∀ {n} {f : Fin n → A} → (∀ {i j} → f i ≡ f j → i ≡ j) →
              Unique (tabulate f)
  tabulate⁺ = Setoid.tabulate⁺ (setoid A)

------------------------------------------------------------------------
-- allFin

allFin⁺ : ∀ n → Unique (allFin n)
allFin⁺ n = tabulate⁺ id

------------------------------------------------------------------------
-- filter

module _ {a p} {A : Set a} {P : Pred _ p} (P? : Decidable P) where

  filter⁺ : ∀ {xs} → Unique xs → Unique (filter P? xs)
  filter⁺ = Setoid.filter⁺ (setoid A) P?
