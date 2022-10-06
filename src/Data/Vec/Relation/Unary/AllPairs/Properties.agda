------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to AllPairs
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Relation.Unary.AllPairs.Properties where

open import Data.Vec
import Data.Vec.Properties as Vecₚ
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
import Data.Vec.Relation.Unary.All.Properties as Allₚ
open import Data.Vec.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)
open import Data.Bool.Base using (true; false)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat.Base using (zero; suc; _+_)
open import Function using (_∘_)
open import Level using (Level)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≢_)

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
  map⁺ (x∉xs ∷ xs!) = Allₚ.map⁺ x∉xs ∷ map⁺ xs!

------------------------------------------------------------------------
-- ++

module _ {R : Rel A ℓ} where

  ++⁺ : ∀ {n m xs ys} → AllPairs R {n} xs → AllPairs R {m} ys →
        All (λ x → All (R x) ys) xs → AllPairs R (xs ++ ys)
  ++⁺ []         Rys _              = Rys
  ++⁺ (px ∷ Rxs) Rys (Rxys ∷ Rxsys) = Allₚ.++⁺ px Rxys ∷ ++⁺ Rxs Rys Rxsys

------------------------------------------------------------------------
-- concat

module _ {R : Rel A ℓ} where

  concat⁺ : ∀ {n m xss} → All (AllPairs R {n}) {m} xss →
            AllPairs (λ xs ys → All (λ x → All (R x) ys) xs) xss →
            AllPairs R (concat xss)
  concat⁺ []           []              = []
  concat⁺ (pxs ∷ pxss) (Rxsxss ∷ Rxss) = ++⁺ pxs (concat⁺ pxss Rxss)
    (All.map Allₚ.concat⁺ (Allₚ.All-swap Rxsxss))

------------------------------------------------------------------------
-- take and drop

module _ {R : Rel A ℓ} where

  take⁺ : ∀ {n} m {xs} → AllPairs R {m + n} xs → AllPairs R {m} (take m xs)
  take⁺ zero pxs = []
  take⁺ (suc m) {x ∷ xs} (px ∷ pxs)
    rewrite Vecₚ.unfold-take m x xs = Allₚ.take⁺ m px ∷ take⁺ m pxs

  drop⁺ : ∀ {n} m {xs} → AllPairs R {m + n} xs → AllPairs R {n} (drop m xs)
  drop⁺ zero pxs = pxs
  drop⁺ (suc m) {x ∷ xs} (_ ∷ pxs)
    rewrite Vecₚ.unfold-drop m x xs = drop⁺ m pxs

------------------------------------------------------------------------
-- tabulate

module _ {R : Rel A ℓ} where

  tabulate⁺ : ∀ {n} {f : Fin n → A} → (∀ {i j} → i ≢ j → R (f i) (f j)) →
              AllPairs R (tabulate f)
  tabulate⁺ {zero}  fᵢ~fⱼ = []
  tabulate⁺ {suc n} fᵢ~fⱼ =
    Allₚ.tabulate⁺ (λ j → fᵢ~fⱼ λ()) ∷
    tabulate⁺ (fᵢ~fⱼ ∘ (_∘ suc-injective))
