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
import Data.List.Relation.Binary.Equality.Setoid as Equality
import Data.List.Relation.Binary.Sublist.Setoid as Sublist
import Data.List.Relation.Binary.Sublist.Setoid.Properties as SublistProperties
import Data.List.Relation.Binary.Permutation.Setoid as Permutation
import Data.List.Relation.Binary.Permutation.Setoid.Properties as PermutationProperties
import Data.List.Relation.Binary.Pointwise as Pointwise
open import Data.List.Relation.Unary.Sorted.TotalOrder as Sorted hiding (head)

open import Data.Fin.Base as Fin hiding (_<_; _≤_)
import Data.Fin.Properties as Fin
open import Data.Fin.Permutation
open import Data.Product using (_,_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Maybe.Relation.Binary.Connected using (Connected; just)
open import Data.Nat.Base as ℕ using (ℕ; z≤n; s≤s; zero; suc)
import Data.Nat.Properties as ℕ
open import Function.Base using (_∘_; const)
open import Function.Bundles using (Inverse)
open import Function.Consequences.Propositional using (inverseʳ⇒injective)
open import Level using (Level)
open import Relation.Binary.Core using (_Preserves_⟶_; Rel)
open import Relation.Binary.Bundles using (TotalOrder; DecTotalOrder; Preorder)
import Relation.Binary.Properties.TotalOrder as TotalOrderProperties
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (contradiction)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

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

  applyUpTo⁺₁ : ∀ f n → (∀ {i} → suc i ℕ.< n → f i ≤ f (suc i)) →
                Sorted O (applyUpTo f n)
  applyUpTo⁺₁ = Linked.applyUpTo⁺₁

  applyUpTo⁺₂ : ∀ f n → (∀ i → f i ≤ f (suc i)) →
                Sorted O (applyUpTo f n)
  applyUpTo⁺₂ = Linked.applyUpTo⁺₂

------------------------------------------------------------------------
-- applyDownFrom

module _ (O : TotalOrder a ℓ₁ ℓ₂) where
  open TotalOrder O

  applyDownFrom⁺₁ : ∀ f n → (∀ {i} → suc i ℕ.< n → f (suc i) ≤ f i) →
                    Sorted O (applyDownFrom f n)
  applyDownFrom⁺₁ = Linked.applyDownFrom⁺₁

  applyDownFrom⁺₂ : ∀ f n → (∀ i → f (suc i) ≤ f i) →
                    Sorted O (applyDownFrom f n)
  applyDownFrom⁺₂ = Linked.applyDownFrom⁺₂


------------------------------------------------------------------------
-- merge

module _ (DO : DecTotalOrder a ℓ₁ ℓ₂) where
  open DecTotalOrder DO using (_≤_; _≤?_) renaming (totalOrder to O)
  open TotalOrderProperties O using (≰⇒≥)

  private
    merge-con : ∀ {v xs ys} →
                Connected _≤_ (just v) (head xs) →
                Connected _≤_ (just v) (head ys) →
                Connected _≤_ (just v) (head (merge _≤?_ xs ys))
    merge-con {xs = []}              cxs cys = cys
    merge-con {xs = x ∷ xs} {[]}     cxs cys = cxs
    merge-con {xs = x ∷ xs} {y ∷ ys} cxs cys with x ≤? y
    ... | yes x≤y = cxs
    ... | no  x≰y = cys

  merge⁺ : ∀ {xs ys} → Sorted O xs → Sorted O ys → Sorted O (merge _≤?_ xs ys)
  merge⁺ {[]}              rxs rys = rys
  merge⁺ {x ∷ xs} {[]}     rxs rys = rxs
  merge⁺ {x ∷ xs} {y ∷ ys} rxs rys
   with x ≤? y  | merge⁺ (Linked.tail rxs) rys
                      | merge⁺ rxs (Linked.tail rys)
  ... | yes x≤y | rec | _   = merge-con (head′ rxs)      (just x≤y)  ∷′ rec
  ... | no  x≰y | _   | rec = merge-con (just (≰⇒≥ x≰y)) (head′ rys) ∷′ rec

  -- Reexport ⊆-mergeˡʳ

  S = Preorder.Eq.setoid (DecTotalOrder.preorder DO)
  open Sublist S using (_⊆_)
  module SP = SublistProperties S

  ⊆-mergeˡ : ∀ xs ys → xs ⊆ merge _≤?_ xs ys
  ⊆-mergeˡ = SP.⊆-mergeˡ _≤?_

  ⊆-mergeʳ : ∀ xs ys → ys ⊆ merge _≤?_ xs ys
  ⊆-mergeʳ = SP.⊆-mergeʳ _≤?_

------------------------------------------------------------------------
-- filter

module _ (O : TotalOrder a ℓ₁ ℓ₂) {P : Pred _ p} (P? : Decidable P) where
  open TotalOrder O

  filter⁺ : ∀ {xs} → Sorted O xs → Sorted O (filter P? xs)
  filter⁺ = Linked.filter⁺ P? trans

------------------------------------------------------------------------
-- lookup

module _ (O : TotalOrder a ℓ₁ ℓ₂) where
  open TotalOrder O

  lookup-mono-≤ : ∀ {xs} → Sorted O xs →
                  ∀ {i j} → i Fin.≤ j → lookup xs i ≤ lookup xs j
  lookup-mono-≤ {x ∷ xs} xs↗ {zero}  {zero}  z≤n       = refl
  lookup-mono-≤ {x ∷ xs} xs↗ {zero}  {suc j} z≤n       = Linked.lookup trans xs↗ (just refl) (suc j)
  lookup-mono-≤ {x ∷ xs} xs↗ {suc i} {suc j} (s≤s i≤j) = lookup-mono-≤ (Sorted.tail O {y = x} xs↗) i≤j

------------------------------------------------------------------------
-- Relationship to binary relations
------------------------------------------------------------------------

module _ (O : TotalOrder a ℓ₁ ℓ₂) where
  open TotalOrder O
  open Equality Eq.setoid
  open Permutation Eq.setoid hiding (refl; trans)
  open PermutationProperties Eq.setoid
  open PosetReasoning poset

  -- Proof that any two sorted lists that are a permutation of each
  -- other are pointwise equal
  ↗↭↗⇒≋ : ∀ {xs ys} → Sorted O xs → Sorted O ys → xs ↭ ys → xs ≋ ys
  ↗↭↗⇒≋ {xs} {ys} xs↗ ys↗ xs↭ys = Pointwise.lookup⁻
    (xs↭ys⇒|xs|≡|ys| xs↭ys)
    (λ i≡j → antisym
      (↗↭↗⇒≤ (↭-sym xs↭ys) ys↗ xs↗ (≡.sym i≡j))
      (↗↭↗⇒≤ xs↭ys  xs↗ ys↗ i≡j))
    where
    ↗↭↗⇒≤ : ∀ {xs ys}
              (xs↭ys : xs ↭ ys) →
              Sorted O xs → Sorted O ys →
              ∀ {i j} → toℕ i ≡ toℕ j →
              lookup ys j ≤ lookup xs i
    ↗↭↗⇒≤ {xs} {ys} xs↭ys xs↗ ys↗ {i} {j} i≡j
      with Fin.injective⇒existsPivot (inverseʳ⇒injective _ (Inverse.inverseʳ (onIndices xs↭ys))) i
    ... | (k , k≤i , i≤π[k]) = begin
      lookup ys j                         ≤⟨ lookup-mono-≤ O ys↗ (≡.subst (ℕ._≤ _) i≡j i≤π[k]) ⟩
      lookup ys (onIndices xs↭ys ⟨$⟩ʳ k)  ≈⟨ onIndices-lookup xs↭ys k ⟨
      lookup xs k                         ≤⟨ lookup-mono-≤ O xs↗ k≤i ⟩
      lookup xs i                         ∎
