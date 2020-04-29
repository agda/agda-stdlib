------------------------------------------------------------------------
-- The Agda standard library
--
-- An implementation of quicksort along with proofs of correctness.
------------------------------------------------------------------------

-- Unless you are need a particular property of QuickSort, you should
-- import and use the sorting algorithm from `Data.List.Sort` instead
-- of this file.

{-# OPTIONS --without-K --safe #-}

open import Data.List.Base
open import Data.List.Properties using (length-partition)
open import Data.List.Relation.Unary.Linked using ([]; [-])
import Data.List.Relation.Unary.Sorted.TotalOrder.Properties as Sorted
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All.Properties as All
open import Data.Maybe.Base using (just)
import Data.Maybe.Relation.Unary.All as All
import Data.Maybe.Relation.Unary.All.Properties as All
import Data.Maybe.Relation.Binary.Connected as Maybe
open import Data.Nat using (_<_; s≤s)
open import Data.Nat.Induction
open import Data.Product as Prod using (_,_)
open import Function.Base using (_∘_)
open import Relation.Binary using (DecTotalOrder)
open import Relation.Nullary using (¬_)

module Data.List.Sort.QuickSort
  {a ℓ₁ ℓ₂} (O : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder O renaming (Carrier to A)

open import Data.List.Sort.Base totalOrder
open import Data.List.Relation.Unary.Sorted.TotalOrder totalOrder hiding (head)
open import Data.List.Relation.Binary.Permutation.Setoid Eq.setoid
import Data.List.Relation.Binary.Permutation.Setoid.Properties Eq.setoid as Perm
open import Relation.Binary.Properties.DecTotalOrder O using (_≰_; ≰⇒≥; ≰-respˡ-≈)

open PermutationReasoning

------------------------------------------------------------------------
-- Definition

sort′ : (xs : List A) → Acc _<_ (length xs) → List A
sort′ []       _         = []
sort′ (x ∷ xs) (acc rec)
  with partition (_≤? x) xs | length-partition (_≤? x) xs
... | ys , zs | ∣ys∣≤∣xs∣ , ∣zs∣≤∣xs∣ =
  sort′ ys (rec _ (s≤s ∣ys∣≤∣xs∣))
  ++ [ x ] ++
  sort′ zs (rec _ (s≤s ∣zs∣≤∣xs∣))

sort : List A → List A
sort xs = sort′ xs (<-wellFounded (length xs))

------------------------------------------------------------------------
-- Properties

private

  sort′-↭ : ∀ xs (rec : Acc _<_ (length xs)) → sort′ xs rec ↭ xs
  sort′-↭ []       _         = ↭-refl
  sort′-↭ (x ∷ xs) (acc rec)
    with partition (_≤? x) xs | length-partition (_≤? x) xs | Perm.partition-↭ (_≤? x) xs
  ... | ys , zs | ∣ys∣≤∣xs∣ , ∣zs∣≤∣xs∣ | partition-↭ = begin
    ql[ys] ++ [ x ] ++ qr[zs] ↭⟨ Perm.shift Eq.refl ql[ys] qr[zs] ⟩
    x ∷ ql[ys] ++ qr[zs]      <⟨ Perm.++⁺ (sort′-↭ ys _) (sort′-↭ zs _) ⟩
    x ∷ ys ++ zs              <⟨ ↭-sym partition-↭ ⟩
    x ∷ xs                    ∎
    where
    ql[ys] = sort′ ys (rec _ (s≤s ∣ys∣≤∣xs∣))
    qr[zs] = sort′ zs (rec _ (s≤s ∣zs∣≤∣xs∣))

  sort′-↗ : ∀ xs (rec : Acc _<_ (length xs)) → Sorted (sort′ xs rec)
  sort′-↗ []       _         = []
  sort′-↗ (x ∷ xs) (acc rec)
    with partition (_≤? x) xs | length-partition (_≤? x) xs | All.partition-All (_≤? x) xs
  ... | ys , zs | ∣ys∣≤∣xs∣ , ∣zs∣≤∣xs∣ | ys≤x , zs≰x =
    Sorted.++⁺ totalOrder (sort′-↗ ys _) q[ys]⇼x
      (Sorted.++⁺ totalOrder [-] x⇼q[zs] (sort′-↗ zs _))
    where
    q[ys]≤x : All (_≤ x) (sort′ ys _)
    q[ys]≤x = Perm.All-resp-↭ ≤-respˡ-≈ (↭-sym (sort′-↭ ys _)) ys≤x

    q[zs]≰x : All (_≰ x) (sort′ zs _)
    q[zs]≰x = Perm.All-resp-↭ ≰-respˡ-≈ (↭-sym (sort′-↭ zs _)) zs≰x

    q[ys]⇼x : Maybe.Connected _≤_ (last (sort′ ys _)) (just x)
    q[ys]⇼x = All.All⇒Connectedʳ (All.last⁺ q[ys]≤x)

    x⇼q[zs] : Maybe.Connected _≤_ (just x) (head (sort′ zs _))
    x⇼q[zs] = All.All⇒Connectedˡ (All.map ≰⇒≥ (All.head⁺ q[zs]≰x))

sort-↭ : ∀ xs → sort xs ↭ xs
sort-↭ xs = sort′-↭ xs _

sort-↗ : ∀ xs → Sorted (sort xs)
sort-↗ xs = sort′-↗ xs _

algorithm : SortingAlgorithm
algorithm = record
  { sort   = sort
  ; sort-↭ = sort-↭
  ; sort-↗ = sort-↗
  }
