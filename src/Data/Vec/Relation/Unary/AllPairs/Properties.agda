------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to AllPairs
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Relation.Unary.AllPairs.Properties where

open import Data.Vec.Base using (_∷_; map; _++_; concat; take; drop; tabulate)
import Data.Vec.Properties as Vec
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
import Data.Vec.Relation.Unary.All.Properties as All
open import Data.Vec.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)
open import Data.Bool.Base using (true; false)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat.Base using (zero; suc; _+_)
open import Function.Base using (_∘_)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core using (_≢_)

private
  variable
    a b c p ℓ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for vector operations
------------------------------------------------------------------------
-- map

module _ {R : Rel A ℓ} {f : B → A} where

  map⁺ : ∀ {n xs} → AllPairs (λ x y → R (f x) (f y)) {n} xs →
         AllPairs R {n} (map f xs)
  map⁺ []           = []
  map⁺ (x∉xs ∷ xs!) = All.map⁺ x∉xs ∷ map⁺ xs!

------------------------------------------------------------------------
-- ++

module _ {R : Rel A ℓ} where

  ++⁺ : ∀ {n m xs ys} → AllPairs R {n} xs → AllPairs R {m} ys →
        All (λ x → All (R x) ys) xs → AllPairs R (xs ++ ys)
  ++⁺ []         Rys _              = Rys
  ++⁺ (px ∷ Rxs) Rys (Rxys ∷ Rxsys) = All.++⁺ px Rxys ∷ ++⁺ Rxs Rys Rxsys

------------------------------------------------------------------------
-- concat

module _ {R : Rel A ℓ} where

  concat⁺ : ∀ {n m xss} → All (AllPairs R {n}) {m} xss →
            AllPairs (λ xs ys → All (λ x → All (R x) ys) xs) xss →
            AllPairs R (concat xss)
  concat⁺ []           []              = []
  concat⁺ (pxs ∷ pxss) (Rxsxss ∷ Rxss) = ++⁺ pxs (concat⁺ pxss Rxss)
    (All.map All.concat⁺ (All.All-swap Rxsxss))

------------------------------------------------------------------------
-- take and drop

module _ {R : Rel A ℓ} where

  take⁺ : ∀ {n} m {xs} → AllPairs R {m + n} xs → AllPairs R {m} (take m xs)
  take⁺ zero pxs = []
  take⁺ (suc m) {x ∷ xs} (px ∷ pxs) = All.take⁺ m px ∷ take⁺ m pxs

  drop⁺ : ∀ {n} m {xs} → AllPairs R {m + n} xs → AllPairs R {n} (drop m xs)
  drop⁺ zero pxs = pxs
  drop⁺ (suc m) (_ ∷ pxs) = drop⁺ m pxs

------------------------------------------------------------------------
-- tabulate

module _ {R : Rel A ℓ} where

  tabulate⁺ : ∀ {n} {f : Fin n → A} → (∀ {i j} → i ≢ j → R (f i) (f j)) →
              AllPairs R (tabulate f)
  tabulate⁺ {zero}  fᵢ~fⱼ = []
  tabulate⁺ {suc n} fᵢ~fⱼ =
    All.tabulate⁺ (λ j → fᵢ~fⱼ λ()) ∷
    tabulate⁺ (fᵢ~fⱼ ∘ (_∘ suc-injective))
