------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Linked
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Unary.Linked.Properties where

open import Data.Bool.Base using (true; false)
open import Data.List.Base hiding (any)
open import Data.List.Relation.Unary.AllPairs as AllPairs
  using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.AllPairs.Properties as AllPairs
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Linked as Linked
  using (Linked; []; [-]; _∷_)
open import Data.Nat.Base using (zero; suc; _<_; z<s; s<s)
open import Data.Nat.Properties using (≤-refl; ≤-pred; m≤n⇒m≤1+n)
open import Data.Maybe.Relation.Binary.Connected
  using (Connected; just; nothing; just-nothing; nothing-just)
open import Level using (Level)
open import Function.Base using (_∘_; flip; _on_)
open import Relation.Binary using (Rel; Transitive; DecSetoid)
open import Relation.Binary.PropositionalEquality.Core using (_≢_)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary.Decidable using (yes; no; does)

private
  variable
    a b p ℓ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Relationship to other predicates
------------------------------------------------------------------------

module _ {R : Rel A ℓ} where

  AllPairs⇒Linked : ∀ {xs} → AllPairs R xs → Linked R xs
  AllPairs⇒Linked []                    = []
  AllPairs⇒Linked (px ∷ [])             = [-]
  AllPairs⇒Linked ((px ∷ _) ∷ py ∷ pxs) =
    px ∷ (AllPairs⇒Linked (py ∷ pxs))

module _ {R : Rel A ℓ} (trans : Transitive R) where

  Linked⇒All : ∀ {v x xs} → R v x →
               Linked R (x ∷ xs) → All (R v) (x ∷ xs)
  Linked⇒All Rvx [-]         = Rvx ∷ []
  Linked⇒All Rvx (Rxy ∷ Rxs) = Rvx ∷ Linked⇒All (trans Rvx Rxy) Rxs

  Linked⇒AllPairs : ∀ {xs} → Linked R xs → AllPairs R xs
  Linked⇒AllPairs []          = []
  Linked⇒AllPairs [-]         = [] ∷ []
  Linked⇒AllPairs (Rxy ∷ Rxs) = Linked⇒All Rxy Rxs ∷ Linked⇒AllPairs Rxs

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for list operations
------------------------------------------------------------------------
-- map

module _ {R : Rel A ℓ} {f : B → A} where

  map⁺ : ∀ {xs} → Linked (R on f) xs → Linked R (map f xs)
  map⁺ []           = []
  map⁺ [-]          = [-]
  map⁺ (Rxy ∷ Rxs)  = Rxy ∷ map⁺ Rxs

  map⁻ : ∀ {xs} → Linked R (map f xs) → Linked (R on f) xs
  map⁻ {[]}         []           = []
  map⁻ {x ∷ []}     [-]          = [-]
  map⁻ {x ∷ y ∷ xs} (Rxy ∷ Rxs)  = Rxy ∷ map⁻ Rxs

------------------------------------------------------------------------
-- _++_

module _ {R : Rel A ℓ} where

  ++⁺ : ∀ {xs ys} →
        Linked R xs →
        Connected R (last xs) (head ys) →
        Linked R ys →
        Linked R (xs ++ ys)
  ++⁺ []          _          Rys         = Rys
  ++⁺ [-]         _          []          = [-]
  ++⁺ [-]         (just Rxy) [-]         = Rxy ∷ [-]
  ++⁺ [-]         (just Rxy) (Ryz ∷ Rys) = Rxy ∷ Ryz ∷ Rys
  ++⁺ (Rxy ∷ Rxs) Rxsys      Rys         = Rxy ∷ ++⁺ Rxs Rxsys Rys

------------------------------------------------------------------------
-- applyUpTo

module _ {R : Rel A ℓ} where

  applyUpTo⁺₁ : ∀ f n → (∀ {i} → suc i < n → R (f i) (f (suc i))) →
                Linked R (applyUpTo f n)
  applyUpTo⁺₁ f 0               Rf = []
  applyUpTo⁺₁ f 1               Rf = [-]
  applyUpTo⁺₁ f (suc n@(suc _)) Rf =
    Rf (s<s z<s) ∷ (applyUpTo⁺₁ (f ∘ suc) n (Rf ∘ s<s))

  applyUpTo⁺₂ : ∀ f n → (∀ i → R (f i) (f (suc i))) →
                Linked R (applyUpTo f n)
  applyUpTo⁺₂ f n Rf = applyUpTo⁺₁ f n (λ _ → Rf _)

------------------------------------------------------------------------
-- applyDownFrom

module _ {R : Rel A ℓ} where

  applyDownFrom⁺₁ : ∀ f n → (∀ {i} → suc i < n → R (f (suc i)) (f i)) →
                    Linked R (applyDownFrom f n)
  applyDownFrom⁺₁ f 0               Rf = []
  applyDownFrom⁺₁ f 1               Rf = [-]
  applyDownFrom⁺₁ f (suc n@(suc _)) Rf =
    Rf ≤-refl ∷ applyDownFrom⁺₁ f n (Rf ∘ m≤n⇒m≤1+n)

  applyDownFrom⁺₂ : ∀ f n → (∀ i → R (f (suc i)) (f i)) →
                    Linked R (applyDownFrom f n)
  applyDownFrom⁺₂ f n Rf = applyDownFrom⁺₁ f n (λ _ → Rf _)

------------------------------------------------------------------------
-- filter

module _ {P : Pred A p} (P? : Decidable P)
         {R : Rel A ℓ} (trans : Transitive R)
         where

  ∷-filter⁺ : ∀ {x xs} → Linked R (x ∷ xs) → Linked R (x ∷ filter P? xs)
  ∷-filter⁺ [-] = [-]
  ∷-filter⁺ {xs = y ∷ _} (r ∷ [-]) with does (P? y)
  ... | false = [-]
  ... | true  = r ∷ [-]
  ∷-filter⁺ {x = x} {xs = y ∷ ys} (r ∷ r′ ∷ rs)
    with does (P? y) | ∷-filter⁺ {xs = ys} | ∷-filter⁺ (r′ ∷ rs)
  ... | false | ihf | _   = ihf (trans r r′ ∷ rs)
  ... | true  | _   | iht = r ∷ iht

  filter⁺   : ∀ {xs} → Linked R xs → Linked R (filter P? xs)
  filter⁺ [] = []
  filter⁺ {xs = x ∷ []} [-] with does (P? x)
  ... | false = []
  ... | true  = [-]
  filter⁺ {xs = x ∷ _} (r ∷ rs) with does (P? x)
  ... | false = filter⁺ rs
  ... | true  = ∷-filter⁺ (r ∷ rs)
