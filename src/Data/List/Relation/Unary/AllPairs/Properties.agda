------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to AllPairs
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.AllPairs.Properties where

open import Data.List.Base using (List; []; _∷_; map; _++_; concat; take; drop;
  applyUpTo; applyDownFrom; tabulate; filter; catMaybes)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties as All using (Any-catMaybes⁺)
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)
open import Data.Bool.Base using (true; false)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Maybe.Relation.Binary.Pointwise using (pointwise⊆any; Pointwise)
open import Data.Fin.Base as F using (Fin)
open import Data.Fin.Properties using (suc-injective; <⇒≢)
open import Data.Nat.Base using (zero; suc; _<_; z≤n; s≤s; z<s; s<s)
open import Data.Nat.Properties using (≤-refl; m<n⇒m<1+n)
open import Function.Base using (_∘_; flip; _on_)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (DecSetoid)
open import Relation.Binary.PropositionalEquality.Core using (_≢_)
open import Relation.Unary using (Pred; Decidable; _⊆_)
open import Relation.Nullary.Decidable.Core using (does)

private
  variable
    a b c p ℓ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for list operations
------------------------------------------------------------------------
-- map

module _ {R : Rel A ℓ} {f : B → A} where

  map⁺ : ∀ {xs} → AllPairs (R on f) xs → AllPairs R (map f xs)
  map⁺ []           = []
  map⁺ (x∉xs ∷ xs!) = All.map⁺ x∉xs ∷ map⁺ xs!

  map⁻ : ∀ {xs} → AllPairs R (map f xs) → AllPairs (R on f) xs
  map⁻ {[]}     _              = []
  map⁻ {_ ∷ _} (fx∉fxs ∷ fxs!) = All.map⁻ fx∉fxs ∷ map⁻ fxs!

------------------------------------------------------------------------
-- ++

module _ {R : Rel A ℓ} where

  ++⁺ : ∀ {xs ys} → AllPairs R xs → AllPairs R ys →
        All (λ x → All (R x) ys) xs → AllPairs R (xs ++ ys)
  ++⁺ []         Rys _              = Rys
  ++⁺ (px ∷ Rxs) Rys (Rxys ∷ Rxsys) = All.++⁺ px Rxys ∷ ++⁺ Rxs Rys Rxsys

------------------------------------------------------------------------
-- concat

module _ {R : Rel A ℓ} where

  concat⁺ : ∀ {xss} → All (AllPairs R) xss →
            AllPairs (λ xs ys → All (λ x → All (R x) ys) xs) xss →
            AllPairs R (concat xss)
  concat⁺ []           []              = []
  concat⁺ (pxs ∷ pxss) (Rxsxss ∷ Rxss) = ++⁺ pxs (concat⁺ pxss Rxss)
    (All.map All.concat⁺ (All.All-swap Rxsxss))

------------------------------------------------------------------------
-- take and drop

module _ {R : Rel A ℓ} where

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

module _ {R : Rel A ℓ} where

  applyUpTo⁺₁ : ∀ f n → (∀ {i j} → i < j → j < n → R (f i) (f j)) → AllPairs R (applyUpTo f n)
  applyUpTo⁺₁ f zero    Rf = []
  applyUpTo⁺₁ f (suc n) Rf =
    All.applyUpTo⁺₁ _ n (Rf (s≤s z≤n) ∘ s≤s) ∷
    applyUpTo⁺₁ _ n (λ i≤j j<n → Rf (s≤s i≤j) (s≤s j<n))

  applyUpTo⁺₂ : ∀ f n → (∀ i j → R (f i) (f j)) → AllPairs R (applyUpTo f n)
  applyUpTo⁺₂ f n Rf = applyUpTo⁺₁ f n (λ _ _ → Rf _ _)

------------------------------------------------------------------------
-- applyDownFrom

module _ {R : Rel A ℓ} where

  applyDownFrom⁺₁ : ∀ f n → (∀ {i j} → j < i → i < n → R (f i) (f j)) →
                    AllPairs R (applyDownFrom f n)
  applyDownFrom⁺₁ f zero    Rf = []
  applyDownFrom⁺₁ f (suc n) Rf =
    All.applyDownFrom⁺₁ _ n (flip Rf ≤-refl)  ∷
    applyDownFrom⁺₁ f n (λ j<i i<n → Rf j<i (m<n⇒m<1+n i<n))

  applyDownFrom⁺₂ : ∀ f n → (∀ i j → R (f i) (f j)) → AllPairs R (applyDownFrom f n)
  applyDownFrom⁺₂ f n Rf = applyDownFrom⁺₁ f n (λ _ _ → Rf _ _)

------------------------------------------------------------------------
-- tabulate

module _ {R : Rel A ℓ} where

  tabulate⁺-< : ∀ {n} {f : Fin n → A} → (∀ {i j} → i F.< j → R (f i) (f j)) →
              AllPairs R (tabulate f)
  tabulate⁺-< {zero}  fᵢ~fⱼ = []
  tabulate⁺-< {suc n} fᵢ~fⱼ =
    All.tabulate⁺ (λ _ → fᵢ~fⱼ z<s) ∷
    tabulate⁺-< (fᵢ~fⱼ ∘ s<s)

  tabulate⁺ : ∀ {n} {f : Fin n → A} → (∀ {i j} → i ≢ j → R (f i) (f j)) →
              AllPairs R (tabulate f)
  tabulate⁺ fᵢ~fⱼ = tabulate⁺-< (fᵢ~fⱼ ∘ <⇒≢)

------------------------------------------------------------------------
-- filter

module _ {R : Rel A ℓ} {P : Pred A p} (P? : Decidable P) where

  filter⁺ : ∀ {xs} → AllPairs R xs → AllPairs R (filter P? xs)
  filter⁺ {_}      []           = []
  filter⁺ {x ∷ xs} (x∉xs ∷ xs!) with does (P? x)
  ... | false = filter⁺ xs!
  ... | true  = All.filter⁺ P? x∉xs ∷ filter⁺ xs!

------------------------------------------------------------------------
-- catMaybes

module _ {R : Rel A ℓ} where

  catMaybes⁺ : {xs : List (Maybe A)} → AllPairs (Pointwise R) xs → AllPairs R (catMaybes xs)
  catMaybes⁺ {xs = []} [] = []
  catMaybes⁺ {xs = nothing ∷  _} (x∼xs ∷ pxs) = catMaybes⁺ pxs
  catMaybes⁺ {xs = just x  ∷ xs} (x∼xs ∷ pxs) = Any-catMaybes⁺ (All.map pointwise⊆any x∼xs) ∷ catMaybes⁺ pxs
