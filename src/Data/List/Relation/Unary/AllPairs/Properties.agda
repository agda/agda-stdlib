------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to AllPairs
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.AllPairs.Properties where

open import Data.List hiding (any)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat using (zero; suc; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-step)
open import Function using (_∘_; flip)
open import Relation.Binary using (Rel; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for list operations
------------------------------------------------------------------------
-- map

module _ {a b ℓ} {A : Set a} {B : Set b} {R : Rel A ℓ} {f : B → A} where

  map⁺ : ∀ {xs} → AllPairs (λ x y → R (f x) (f y)) xs →
         AllPairs R (map f xs)
  map⁺ []           = []
  map⁺ (x∉xs ∷ xs!) = All.map⁺ x∉xs ∷ map⁺ xs!

------------------------------------------------------------------------
-- ++

module _ {a ℓ} {A : Set a} {R : Rel A ℓ} where

  ++⁺ : ∀ {xs ys} → AllPairs R xs → AllPairs R ys →
        All (λ x → All (R x) ys) xs → AllPairs R (xs ++ ys)
  ++⁺ []         Rys _              = Rys
  ++⁺ (px ∷ Rxs) Rys (Rxys ∷ Rxsys) = All.++⁺ px Rxys ∷ ++⁺ Rxs Rys Rxsys

------------------------------------------------------------------------
-- concat

module _ {a ℓ} {A : Set a} {R : Rel A ℓ} where

  concat⁺ : ∀ {xss} → All (AllPairs R) xss →
            AllPairs (λ xs ys → All (λ x → All (R x) ys) xs) xss →
            AllPairs R (concat xss)
  concat⁺ []           []              = []
  concat⁺ (pxs ∷ pxss) (Rxsxss ∷ Rxss) = ++⁺ pxs (concat⁺ pxss Rxss)
    (All.map All.concat⁺ (All.All-swap Rxsxss))

------------------------------------------------------------------------
-- take and drop

module _ {a ℓ} {A : Set a} {R : Rel A ℓ} where

  take⁺ : ∀ {xs} n → AllPairs R xs → AllPairs R (take n xs)
  take⁺ zero    pxs        = []
  take⁺ (suc n) []         = []
  take⁺ (suc n) (px ∷ pxs) = All.take⁺ n px ∷ take⁺ n pxs

  drop⁺ : ∀ {xs} n → AllPairs R xs → AllPairs R (drop n xs)
  drop⁺ zero    pxs       = pxs
  drop⁺ (suc n) []        = []
  drop⁺ (suc n) (_ ∷ pxs) = drop⁺ n pxs

------------------------------------------------------------------------
-- applyUpTo

module _ {a ℓ} {A : Set a} {R : Rel A ℓ} where

  applyUpTo⁺₁ : ∀ f n → (∀ {i j} → i < j → j < n → R (f i) (f j)) → AllPairs R (applyUpTo f n)
  applyUpTo⁺₁ f zero    Rf = []
  applyUpTo⁺₁ f (suc n) Rf =
    All.applyUpTo⁺₁ _ n (Rf (s≤s z≤n) ∘ s≤s) ∷
    applyUpTo⁺₁ _ n (λ i≤j j<n → Rf (s≤s i≤j) (s≤s j<n))

  applyUpTo⁺₂ : ∀ f n → (∀ i j → R (f i) (f j)) → AllPairs R (applyUpTo f n)
  applyUpTo⁺₂ f n Rf = applyUpTo⁺₁ f n (λ _ _ → Rf _ _)

------------------------------------------------------------------------
-- applyDownFrom

module _ {a ℓ} {A : Set a} {R : Rel A ℓ} where

  applyDownFrom⁺₁ : ∀ f n → (∀ {i j} → j < i → i < n → R (f i) (f j)) →
                    AllPairs R (applyDownFrom f n)
  applyDownFrom⁺₁ f zero    Rf = []
  applyDownFrom⁺₁ f (suc n) Rf =
    All.applyDownFrom⁺₁ _ n (flip Rf ≤-refl)  ∷
    applyDownFrom⁺₁ f n (λ j<i i<n → Rf j<i (≤-step i<n))

  applyDownFrom⁺₂ : ∀ f n → (∀ i j → R (f i) (f j)) → AllPairs R (applyDownFrom f n)
  applyDownFrom⁺₂ f n Rf = applyDownFrom⁺₁ f n (λ _ _ → Rf _ _)

------------------------------------------------------------------------
-- tabulate

module _ {a ℓ} {A : Set a} {R : Rel A ℓ} where

  tabulate⁺ : ∀ {n} {f : Fin n → A} → (∀ {i j} → i ≢ j → R (f i) (f j)) →
              AllPairs R (tabulate f)
  tabulate⁺ {zero}  fᵢ~fⱼ = []
  tabulate⁺ {suc n} fᵢ~fⱼ =
    All.tabulate⁺ (λ j → fᵢ~fⱼ λ()) ∷
    tabulate⁺ (fᵢ~fⱼ ∘ (_∘ suc-injective))

------------------------------------------------------------------------
-- filter

module _ {a ℓ p} {A : Set a} {R : Rel A ℓ}
         {P : Pred A p} (P? : Decidable P) where

  filter⁺ : ∀ {xs} → AllPairs R xs → AllPairs R (filter P? xs)
  filter⁺ {_}      []           = []
  filter⁺ {x ∷ xs} (x∉xs ∷ xs!) with P? x
  ... | no  _ = filter⁺ xs!
  ... | yes _ = All.filter⁺ P? x∉xs ∷ filter⁺ xs!
