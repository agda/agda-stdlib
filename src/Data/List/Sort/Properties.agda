------------------------------------------------------------------------
-- The Agda standard library
--
-- The core definition of a sorting algorithm
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.List
open import Data.List.Relation.Unary.All using ([]; _∷_; map)
import Data.List.Relation.Unary.Sorted.TotalOrder.Properties as Sorted
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (↭⇒↭ₛ; ↭-empty-inv)
open import Data.List.Relation.Binary.Equality.Propositional using (≋⇒≡)
open import Function.Base using (_∘_)
open import Relation.Binary using (TotalOrder; _Preserves_⟶_; _Respects_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Unary using (Pred; Decidable)

open import Data.List.Sort.Base

module Data.List.Sort.Properties
  {a ℓ₁ ℓ₂} {O : TotalOrder a ℓ₁ ℓ₂}
  (sortingAlgorithm : SortingAlgorithm O) where

open TotalOrder O renaming (Carrier to A)
open SortingAlgorithm sortingAlgorithm

open import Data.List.Relation.Binary.Permutation.Setoid Eq.setoid as Permₛ
  using () renaming (_↭_ to _↭ₛ_; ↭-sym to ↭ₛ-sym)
import Data.List.Relation.Binary.Permutation.Setoid.Properties Eq.setoid as Permₚ
open import Data.List.Relation.Binary.Equality.Setoid Eq.setoid using (_≋_)
open import Data.List.Relation.Unary.Sorted.TotalOrder O
open import Data.List.Relation.Unary.Unique.Setoid Eq.setoid using (Unique)
open import Data.List.Membership.Setoid Eq.setoid using (_∈_)

private
  variable
    x : A
    xs ys : List A

------------------------------------------------------------------------
-- Properties with respect to relations and predicates
------------------------------------------------------------------------
-- Setoid permutations

sort-↭ₛ : ∀ xs → sort xs ↭ₛ xs
sort-↭ₛ xs = ↭⇒↭ₛ Eq.setoid (sort-↭ xs)

sort-pres-↭ₛ : xs ↭ₛ ys → sort xs ↭ₛ sort ys
sort-pres-↭ₛ {xs} {ys} xs↭ys = begin
  sort xs ↭⟨  sort-↭ₛ xs ⟩
  xs      ↭⟨  xs↭ys ⟩
  ys      ↭˘⟨ sort-↭ₛ ys ⟩
  sort ys ∎
  where open Permₛ.PermutationReasoning

------------------------------------------------------------------------
-- Propositional permutations

sort-pres-↭ : xs ↭ ys → sort xs ↭ sort ys
sort-pres-↭ {xs} {ys} xs↭ys = begin
  sort xs ↭⟨  sort-↭ xs ⟩
  xs      ↭⟨  xs↭ys ⟩
  ys      ↭˘⟨ sort-↭ ys ⟩
  sort ys ∎
  where open PermutationReasoning

------------------------------------------------------------------------
-- Pointwise equality

sort-pres-↭ₛ-≋ : xs ↭ₛ ys → sort xs ≋ sort ys
sort-pres-↭ₛ-≋ = Sorted.↗↭↗⇒≋ O (sort-↗ _) (sort-↗ _) ∘ sort-pres-↭ₛ

pres-↭ₛ⇒sort-commute : ∀ {f} → f Preserves _↭ₛ_ ⟶ _↭ₛ_ →
                       (∀ {xs} → Sorted xs → Sorted (f xs)) →
                       ∀ xs → sort (f xs) ≋ f (sort xs)
pres-↭ₛ⇒sort-commute {f = f} pres-↭ pres-↗ xs =
  Sorted.↗↭↗⇒≋ O (sort-↗ (f xs)) (pres-↗ (sort-↗ xs)) (begin
    sort (f xs) ↭⟨  sort-↭ₛ (f xs) ⟩
    f xs        ↭˘⟨ pres-↭ (sort-↭ₛ xs) ⟩
    f (sort xs) ∎)
  where open Permₛ.PermutationReasoning

------------------------------------------------------------------------
-- Propositional equality

sort-[] : sort [] ≡ []
sort-[] = ↭-empty-inv (sort-↭ [])

sort-pres-↭-≡ : xs ↭ ys → sort xs ≡ sort ys
sort-pres-↭-≡ xs↭ys = ≋⇒≡ {!sort-pres-↭ₛ-≋ ?!} --Sorted.↗↭↗⇒≋ O (sort-↗ _) (sort-↗ _) ? -- ∘ sort-pres-↭

pres-↭⇒sort-commute : ∀ {f} → f Preserves _↭_ ⟶ _↭_ →
                       (∀ {xs} → Sorted xs → Sorted (f xs)) →
                       ∀ xs → sort (f xs) ≡ f (sort xs)
pres-↭⇒sort-commute {f = f} pres-↭ pres-↗ xs = {!!}
{-
  Sorted.↗↭↗⇒≋ O (sort-↗ (f xs)) (pres-↗ (sort-↗ xs)) (begin
    sort (f xs) ↭⟨  sort-↭ₛ (f xs) ⟩
    f xs        ↭˘⟨ pres-↭ (sort-↭ₛ xs) ⟩
    f (sort xs) ∎)
-}
  where open Permₛ.PermutationReasoning

------------------------------------------------------------------------
-- Uniqueness

sort!⁺ : Unique xs → Unique (sort xs)
sort!⁺ = Permₚ.Unique-resp-↭ (↭ₛ-sym (sort-↭ₛ _))

sort!⁻ : Unique (sort xs) → Unique xs
sort!⁻ = Permₚ.Unique-resp-↭ (sort-↭ₛ _)

------------------------------------------------------------------------
-- Membership

∈-sort⁺ : x ∈ xs → x ∈ sort xs
∈-sort⁺ = Permₚ.∈-resp-↭ (↭ₛ-sym (sort-↭ₛ _))

∈-sort⁻ : x ∈ sort xs → x ∈ xs
∈-sort⁻ = Permₚ.∈-resp-↭ (sort-↭ₛ _)

------------------------------------------------------------------------
-- Properties of list operations
------------------------------------------------------------------------
-- filter

sort-filter-commute : ∀ {p} {P : Pred A p} (P? : Decidable P) →
                      P Respects _≈_ →
                      ∀ xs → sort (filter P? xs) ≋ filter P? (sort xs)
sort-filter-commute P? resp = pres-↭ₛ⇒sort-commute (Permₚ.filter⁺ P? resp) (Sorted.filter⁺ O P?)
