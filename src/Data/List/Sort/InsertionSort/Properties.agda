------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of insertion sort
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (DecTotalOrder)

module Data.List.Sort.InsertionSort.Properties
  {a ℓ₁ ℓ₂}
  (O : DecTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Bool.Base using (true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_; decidable; setoid)
open import Data.List.Relation.Binary.Permutation.Propositional
import Data.List.Relation.Binary.Permutation.Propositional.Properties as Perm
open import Data.List.Relation.Unary.Linked using ([]; [-]; _∷_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.Properties.DecTotalOrder O using (≰⇒≥)
open import Relation.Nullary.Decidable.Core using (does; yes; no)
open import Relation.Nullary.Negation.Core using (contradiction)

open DecTotalOrder O renaming (Carrier to A; trans to ≤-trans)
  using (totalOrder; _≤?_; _≤_; module Eq; _≈_; ≤-respʳ-≈; ≤-respˡ-≈; antisym)

open import Data.List.Relation.Binary.Equality.Setoid Eq.setoid
  using (_≋_; ≋-refl; ≋-sym; ≋-trans)
open import Data.List.Relation.Unary.Sorted.TotalOrder totalOrder using (Sorted)
open import Data.List.Sort.Base totalOrder using (SortingAlgorithm)
open import Data.List.Sort.InsertionSort.Base O
import Relation.Binary.Reasoning.Setoid (setoid Eq.setoid) as ≋-Reasoning

------------------------------------------------------------------------
-- Permutation property

insert-↭ : ∀ x xs → insert x xs ↭ x ∷ xs
insert-↭ x [] = ↭-refl
insert-↭ x (y ∷ xs) with does (x ≤? y)
... | true  = ↭-refl
... | false = begin
  y ∷ insert x xs ↭⟨ prep y (insert-↭ x xs) ⟩
  y ∷ x ∷ xs      ↭⟨ swap y x refl ⟩
  x ∷ y ∷ xs ∎
  where open PermutationReasoning

insert-cong-↭ : ∀ {x xs ys} → xs ↭ ys → insert x xs ↭ x ∷ ys
insert-cong-↭ {x} {xs} {ys} eq = begin
  insert x xs ↭⟨ insert-↭ x xs ⟩
  x ∷ xs      ↭⟨ prep x eq ⟩
  x ∷ ys ∎
  where open PermutationReasoning

sort-↭ : ∀ (xs : List A) → sort xs ↭ xs
sort-↭ [] = ↭-refl
sort-↭ (x ∷ xs) = insert-cong-↭ (sort-↭ xs)

------------------------------------------------------------------------
-- Sorted property

insert-↗ : ∀ x {xs} → Sorted xs → Sorted (insert x xs)
insert-↗ x [] = [-]
insert-↗ x ([-] {y}) with x ≤? y
... | yes x≤y = x≤y ∷ [-]
... | no  x≰y = ≰⇒≥ x≰y ∷ [-]
insert-↗ x (_∷_ {y} {z} {ys} y≤z z≤ys) with x ≤? y
... | yes x≤y = x≤y ∷ y≤z ∷ z≤ys
... | no  x≰y with ih ← insert-↗ x z≤ys | x ≤? z
... | yes _ = ≰⇒≥ x≰y ∷ ih
... | no  _ = y≤z ∷ ih

sort-↗ : ∀ xs → Sorted (sort xs)
sort-↗ [] = []
sort-↗ (x ∷ xs) = insert-↗ x (sort-↗ xs)

------------------------------------------------------------------------
-- Algorithm

insertionSort : SortingAlgorithm
insertionSort = record
  { sort   = sort
  ; sort-↭ = sort-↭
  ; sort-↗ = sort-↗
  }

------------------------------------------------------------------------
-- Congruence properties

insert-congʳ : ∀ z {xs ys} → xs ≋ ys → insert z xs ≋ insert z ys
insert-congʳ z [] = ≋-refl
insert-congʳ z (_∷_ {x} {y} {xs} {ys} x∼y eq) with z ≤? x | z ≤? y
... | yes  _  | yes  _  = Eq.refl ∷ x∼y ∷ eq
... | no  z≰x | yes z≤y = contradiction (≤-respʳ-≈ (Eq.sym x∼y) z≤y) z≰x
... | yes z≤x | no  z≰y = contradiction (≤-respʳ-≈ x∼y z≤x) z≰y
... | no   _  | no   _  = x∼y ∷ insert-congʳ z eq

insert-congˡ : ∀ {x y} xs → x ≈ y → insert x xs ≋ insert y xs
insert-congˡ {x} {y} [] eq = eq ∷ []
insert-congˡ {x} {y} (z ∷ xs) eq with x ≤? z | y ≤? z
... | yes  _  | yes  _  = eq ∷ ≋-refl
... | no  x≰z | yes y≤z = contradiction (≤-respˡ-≈ (Eq.sym eq) y≤z) x≰z
... | yes x≤z | no  y≰z = contradiction (≤-respˡ-≈ eq x≤z) y≰z
... | no   _  | no   _  = Eq.refl ∷ insert-congˡ xs eq

insert-cong : ∀ {x y xs ys} → x ≈ y → xs ≋ ys → insert x xs ≋ insert y ys
insert-cong {y = y} {xs} eq₁ eq₂ = ≋-trans (insert-congˡ xs eq₁) (insert-congʳ y eq₂)

sort-cong : ∀ {xs ys} → xs ≋ ys → sort xs ≋ sort ys
sort-cong [] = []
sort-cong (x∼y ∷ eq) = insert-cong x∼y (sort-cong eq)

private
  insert-swap-≤ : ∀ {x y} xs → x ≤ y → insert x (insert y xs) ≋ insert y (insert x xs)
  insert-swap-≤ {x} {y} [] x≤y with x ≤? y
  ... | no  xy = contradiction x≤y xy
  ... | yes xy with y ≤? x
  ... | yes yx = Eq.sym eq ∷ eq ∷ [] where eq = antisym yx xy
  ... | no  _  = ≋-refl
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y with y ≤? z
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | yes yz with x ≤? y
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | yes yz | yes xy with x ≤? z
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | yes yz | yes xy | yes xz with y ≤? x
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | yes yz | yes xy | yes xz | yes yx =
    Eq.sym eq ∷ eq ∷ ≋-refl where eq = antisym yx xy
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | yes yz | yes xy | yes xz | no yx with y ≤? z
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | yes yz | yes xy | yes xz | no yx | yes yz' = ≋-refl
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | yes yz | yes xy | yes xz | no yx | no  yz' = contradiction yz yz'
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | yes yz | yes xy | no xz = contradiction (≤-trans xy yz) xz
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | yes yz | no xy = contradiction x≤y xy
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | no  yz with x ≤? z
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | no  yz | yes xz with y ≤? x
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | no  yz | yes xz | yes yx = contradiction (≤-trans yx xz) yz
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | no  yz | yes xz | no  yx with y ≤? z
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | no  yz | yes xz | no  yx | yes yz' = contradiction yz' yz
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | no  yz | yes xz | no  yx | no yz' = ≋-refl
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | no  yz | no  xz with y ≤? z
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | no  yz | no  xz | yes yz' = contradiction yz' yz
  insert-swap-≤ {x} {y} (z ∷ xs) x≤y | no  yz | no  xz | no  yz' = Eq.refl ∷ (insert-swap-≤ xs x≤y)

insert-swap : ∀ x y xs → insert x (insert y xs) ≋ insert y (insert x xs)
insert-swap x y xs with x ≤? y
... | yes x≤y = insert-swap-≤ xs x≤y
... | no  x≰y = ≋-sym (insert-swap-≤ xs (≰⇒≥ x≰y))

insert-swap-cong : ∀ {x y x′ y′ xs ys} → x ≈ x′ → y ≈ y′ → xs ≋ ys →
                   insert x (insert y xs) ≋ insert y′ (insert x′ ys)
insert-swap-cong {x} {y} {x′} {y′} {xs} {ys} eq₁ eq₂ eq₃ = begin
  insert x (insert y xs)   ≈⟨ insert-cong eq₁ (insert-cong eq₂ eq₃) ⟩
  insert x′ (insert y′ ys) ≈⟨ insert-swap x′ y′ ys ⟩
  insert y′ (insert x′ ys) ∎
  where open ≋-Reasoning
