------------------------------------------------------------------------
-- The Agda standard library
--
-- An implementation of insertion sort and its properties.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (DecTotalOrder)

module Data.List.Sort.InsertionSort
  {a ℓ₁ ℓ₂}
  (O : DecTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Bool.Base using (true; false ; if_then_else_)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Function using (id)

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Linked using ([]; [-] ; _∷_)
open import Data.List.Relation.Binary.Pointwise
  using (Pointwise ; [] ; _∷_ ; decidable ; setoid)

open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality
  using (inspect ; [_])
open import Relation.Binary.Properties.DecTotalOrder O
  using (≰⇒≥ ; ≥-antisym)
open import Relation.Nullary.Decidable.Core
  using (does ; yes ; no ; map′)

open DecTotalOrder O
  renaming (Carrier to A ; refl to reflA ; trans to transA)
  using (totalOrder; _≤?_; _≤_
        ; module Eq; _≈_; ≤-respʳ-≈; ≤-respˡ-≈; antisym)
  
open import Data.List.Relation.Binary.Equality.Setoid Eq.setoid
  using (_≋_)
open import Data.List.Relation.Binary.Permutation.Setoid Eq.setoid
open import Data.List.Relation.Unary.Sorted.TotalOrder totalOrder
  using (Sorted)
open import Data.List.Sort.Base totalOrder
open import Relation.Binary.Reasoning.Setoid (setoid Eq.setoid)
  as SetoidReasoning using ()

open Setoid (setoid Eq.setoid)
  renaming (refl to reflₚₜ ; trans to transₚₜ) using ()

------------------------------------------------------------------------
-- Definitions

insert : A → List A → List A
insert x [] = x ∷ []
insert x (y ∷ xs) = if does (x ≤? y)
  then x ∷ y ∷ xs
  else y ∷ insert x xs

sort : List A → List A
sort [] = []
sort (x ∷ xs) = insert x (sort xs)

------------------------------------------------------------------------
-- Permutation property

insert-↭ : ∀ x xs → insert x xs ↭ x ∷ xs
insert-↭ x [] = ↭-refl
insert-↭ x (y ∷ xs) with does (x ≤? y)
... | true = ↭-refl
... | false = begin
  y ∷ insert x xs ↭⟨ prep Eq.refl (insert-↭ x xs) ⟩
  y ∷ x ∷ xs      ↭⟨ swap Eq.refl Eq.refl ↭-refl ⟩
  x ∷ y ∷ xs ∎
  where open PermutationReasoning

insert-cong-↭ : ∀ {x xs x' xs'} → x ≈ x' → xs ↭ xs' →
                insert x xs ↭ x' ∷ xs'
insert-cong-↭ {x} {xs} {x'} {xs'} eq1 eq2 = begin
  insert x xs ↭⟨ insert-↭ x xs ⟩
  x ∷ xs      ↭⟨ prep eq1 eq2 ⟩
  x' ∷ xs' ∎
  where open PermutationReasoning

sort-↭ : ∀ (xs : List A) → sort xs ↭ xs
sort-↭ [] = ↭-refl
sort-↭ (x ∷ xs) = insert-cong-↭ Eq.refl (sort-↭ xs)

------------------------------------------------------------------------
-- Sorted property

insert-↗ : ∀ x {xs} → Sorted xs → Sorted (insert x xs)
insert-↗ x [] = [-]
insert-↗ x ([-] {y}) with (x ≤? y)
... | yes x≤y = x≤y ∷ [-]
... | no x≤y = ≰⇒≥ x≤y ∷ [-]
insert-↗ x (_∷_ {y} {z} {ys} y≤z z≤ys) with (x ≤? y)
... | yes x≤y = x≤y ∷ y≤z ∷ z≤ys
... | no x≤y with insert-↗ x z≤ys
... | sd with (x ≤? z)
... | yes r = ≰⇒≥ x≤y ∷ sd
... | no r = y≤z ∷ sd

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

insert-congʳ : ∀ x {xs ys} → xs ≋ ys → insert x xs ≋ insert x ys
insert-congʳ x [] = Eq.refl ∷ []
insert-congʳ z (_∷_ {x} {y} {xs} {ys} x∼y eq) with z ≤? x | z ≤? y
... | yes z≤x | yes z≤y = Eq.refl ∷ x∼y ∷ eq
... | no z≤x | yes z≤y = ⊥-elim (z≤x (≤-respʳ-≈ (Eq.sym x∼y) z≤y))
... | yes z≤x | no z≤y = ⊥-elim (z≤y (≤-respʳ-≈ x∼y z≤x))
... | no z≤x | no z≤y = x∼y ∷ insert-congʳ z eq

insert-congˡ : ∀ {x y} xs → x ≈ y → insert x xs ≋ insert y xs
insert-congˡ {x} {y} [] eq = eq ∷ []
insert-congˡ {x} {y} (z ∷ xs) eq with x ≤? z | y ≤? z
... | yes x≤z | yes y≤z = eq ∷ reflₚₜ
... | no x≤z | yes y≤z = ⊥-elim (x≤z (≤-respˡ-≈ (Eq.sym eq) y≤z))
... | yes x≤z | no y≤z = ⊥-elim (y≤z (≤-respˡ-≈ eq x≤z))
... | no x≤z | no y≤z = Eq.refl ∷ insert-congˡ xs eq

insert-cong : ∀ {x y xs ys} → x ≈ y → xs ≋ ys →
              insert x xs ≋ insert y ys
insert-cong {x} {y} {xs} {ys} eq1 eq2 =
  transₚₜ (insert-congˡ xs eq1) (insert-congʳ y eq2)

sort-cong : ∀ {xs ys} → xs ≋ ys → sort xs ≋ sort ys
sort-cong [] = []
sort-cong (x∼y ∷ eq) = insert-cong x∼y (sort-cong eq)

insert-swap : ∀ x y xs → insert x (insert y xs) ≋ insert y (insert x xs)
insert-swap x y [] with x ≤? y | y ≤? x
... | yes x≤y | yes y≤x = eq ∷ (Eq.sym eq) ∷ []
  where eq = antisym x≤y y≤x
... | no x≤y | yes y≤x = reflₚₜ
... | yes x≤y | no y≤x = reflₚₜ
... | no x≤y | no y≤x = (Eq.sym eq) ∷ (eq ∷ [])
  where eq = ≥-antisym (≰⇒≥ x≤y) (≰⇒≥ y≤x)
insert-swap x y (z ∷ xs) with x ≤? z in xz | y ≤? z in yz |
  x ≤? y in xy | y ≤? x in yx
insert-swap x y (z ∷ xs) | yes x≤z | yes y≤z | yes x≤y | yes y≤x
  rewrite xy | yx = eq ∷ (Eq.sym eq) ∷ reflₚₜ
  where eq = antisym x≤y y≤x
insert-swap x y (z ∷ xs) | yes x≤z | yes y≤z | yes x≤y | no y≤x
  rewrite xy | yx | yz = reflₚₜ
insert-swap x y (z ∷ xs) | yes x≤z | yes y≤z | no x≤y | yes y≤x
  rewrite xy | yx | xz = reflₚₜ
insert-swap x y (z ∷ xs) | yes x≤z | yes y≤z | no x≤y | no y≤x
  rewrite xy | yx | yz | xz = Eq.sym eq ∷ eq ∷ (reflₚₜ)
  where eq = ≥-antisym (≰⇒≥ x≤y) (≰⇒≥ y≤x)  
insert-swap x y (z ∷ xs) | yes x≤z | no y≤z | yes x≤y | yes y≤x
  rewrite xy | yx | yz | xz = ⊥-elim (y≤z (transA y≤x x≤z))
insert-swap x y (z ∷ xs) | yes x≤z | no y≤z | yes x≤y | no y≤x
  rewrite xy | yx | yz | xz = reflₚₜ
insert-swap x y (z ∷ xs) | yes x≤z | no y≤z | no x≤y | yes y≤x
  rewrite xy | yx | yz | xz = ⊥-elim (y≤z (transA y≤x x≤z))
insert-swap x y (z ∷ xs) | yes x≤z | no y≤z | no x≤y | no y≤x
  rewrite xy | yx | yz | xz = reflₚₜ
insert-swap x y (z ∷ xs) | no x≤z | yes y≤z | yes x≤y | yes y≤x
  rewrite xy | yx | yz | xz = ⊥-elim (x≤z (transA x≤y y≤z))
insert-swap x y (z ∷ xs) | no x≤z | yes y≤z | yes x≤y | no y≤x
  rewrite xy | yx | yz | xz = ⊥-elim (x≤z (transA x≤y y≤z))
insert-swap x y (z ∷ xs) | no x≤z | yes y≤z | no x≤y | yes y≤x
  rewrite xy | yx | yz | xz = reflₚₜ
insert-swap x y (z ∷ xs) | no x≤z | yes y≤z | no x≤y | no y≤x
  rewrite xy | yx | yz | xz = reflₚₜ
insert-swap x y (z ∷ xs) | no x≤z | no y≤z | yes x≤y | yes y≤x
  rewrite xy | yx | yz | xz = Eq.refl ∷ (insert-swap x y xs)
insert-swap x y (z ∷ xs) | no x≤z | no y≤z | yes x≤y | no y≤x
  rewrite xy | yx | yz | xz = Eq.refl ∷ (insert-swap x y xs)
insert-swap x y (z ∷ xs) | no x≤z | no y≤z | no x≤y | yes y≤x
  rewrite xy | yx | yz | xz = Eq.refl ∷ (insert-swap x y xs)
insert-swap x y (z ∷ xs) | no x≤z | no y≤z | no x≤y | no y≤x
  rewrite xy | yx | yz | xz = Eq.refl ∷ (insert-swap x y xs)

insert-swap-cong : ∀ {x y x′ y′ xs ys} →
                   x ≈ x′ → y ≈ y′ → xs ≋ ys →
                   insert x (insert y xs) ≋ insert y′ (insert x′ ys)
insert-swap-cong {x} {y} {x′} {y′} {xs} {ys} eq1 eq2 eq3 = begin
  insert x (insert y xs)   ≈⟨ insert-cong eq1 (insert-cong eq2 eq3) ⟩
  insert x′ (insert y′ ys) ≈⟨ insert-swap x′ y′ ys ⟩
  insert y′ (insert x′ ys) ∎
  where open SetoidReasoning

-- Ideally, we want:

--   property1 : ∀ {xs ys} → xs ↭ ys →
--               Sorted xs → Sorted ys → xs ≋ ys

-- But the induction over xs ↭ ys is hard to do. So instead we have a
-- similar property that depends on the particular sorting algorithm
-- used.

sort-cong-↭ : ∀ {xs ys} → xs ↭ ys → sort xs ≋ sort ys
sort-cong-↭ (refl x) = sort-cong x
sort-cong-↭ (prep eq eq₁) = insert-cong eq (sort-cong-↭ eq₁)
sort-cong-↭ (swap {x = x} {y} {x′} {y′} eq₁ eq₂ eq) =
  insert-swap-cong eq₁ eq₂ (sort-cong-↭ eq)
sort-cong-↭ (trans eq eq₁) =
  transₚₜ (sort-cong-↭ eq) (sort-cong-↭ eq₁)

------------------------------------------------------------------------
-- Decidability property

infix 4 _↭?_

_↭?_ : Decidable _↭_
xs ↭? ys with decidable Eq._≟_ (sort xs) (sort ys)
... | yes eq = yes (begin
  xs      ↭⟨ ↭-sym (sort-↭ xs) ⟩
  sort xs ↭⟨ refl eq ⟩
  sort ys ↭⟨ sort-↭ ys ⟩
  ys ∎)
  where open PermutationReasoning
... | no eq = no (λ x → eq (sort-cong-↭ x))
