------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to AllNeighbours
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.AllNeighbours.Properties where

open import Data.List hiding (any)
open import Data.List.Relation.Unary.AllPairs as AllPairs
  using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllNeighbours as AllNeighbours
  using (AllNeighbours; []; [-]; _∷_)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat using (zero; suc; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-pred; ≤-step)
open import Level using (Level)
open import Function using (_∘_; flip)
open import Relation.Binary using (Rel; Transitive; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (yes; no)

private
  variable
    a b p ℓ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Relationship to other predicates
------------------------------------------------------------------------

module _ {R : Rel A ℓ} where

  AllPairs⇒AllNeighbours : ∀ {xs} → AllPairs R xs → AllNeighbours R xs
  AllPairs⇒AllNeighbours []                    = []
  AllPairs⇒AllNeighbours (px ∷ [])             = [-]
  AllPairs⇒AllNeighbours ((px ∷ _) ∷ py ∷ pxs) =
    px ∷ (AllPairs⇒AllNeighbours (py ∷ pxs))

module _ {R : Rel A ℓ} (trans : Transitive R) where

  AllNeighbours⇒All : ∀ {v x xs} → R v x →
                      AllNeighbours R (x ∷ xs) → All (R v) (x ∷ xs)
  AllNeighbours⇒All Rvx [-]         = Rvx ∷ []
  AllNeighbours⇒All Rvx (Rxy ∷ Rxs) =
    Rvx ∷ AllNeighbours⇒All (trans Rvx Rxy) Rxs

  AllNeighbours⇒AllPairs : ∀ {xs} → AllNeighbours R xs → AllPairs R xs
  AllNeighbours⇒AllPairs []          = []
  AllNeighbours⇒AllPairs [-]         = [] ∷ []
  AllNeighbours⇒AllPairs (Rxy ∷ Rxs) =
    AllNeighbours⇒All Rxy Rxs ∷ AllNeighbours⇒AllPairs Rxs

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for list operations
------------------------------------------------------------------------
-- map

module _ {R : Rel A ℓ} {f : B → A} where

  map⁺ : ∀ {xs} → AllNeighbours (λ x y → R (f x) (f y)) xs →
         AllNeighbours R (map f xs)
  map⁺ []           = []
  map⁺ [-]          = [-]
  map⁺ (Rxy ∷ Rxs)  = Rxy ∷ map⁺ Rxs

------------------------------------------------------------------------
-- applyUpTo

module _ {R : Rel A ℓ} where

  applyUpTo⁺₁ : ∀ f n → (∀ {i} → suc i < n → R (f i) (f (suc i))) →
                AllNeighbours R (applyUpTo f n)
  applyUpTo⁺₁ f zero          Rf = []
  applyUpTo⁺₁ f (suc zero)    Rf = [-]
  applyUpTo⁺₁ f (suc (suc n)) Rf =
    Rf (s≤s (s≤s z≤n)) ∷ (applyUpTo⁺₁ (f ∘ suc) (suc n) (Rf ∘ s≤s))

  applyUpTo⁺₂ : ∀ f n → (∀ i → R (f i) (f (suc i))) →
                AllNeighbours R (applyUpTo f n)
  applyUpTo⁺₂ f n Rf = applyUpTo⁺₁ f n (λ _ → Rf _)

------------------------------------------------------------------------
-- applyDownFrom

module _ {R : Rel A ℓ} where

  applyDownFrom⁺₁ : ∀ f n → (∀ {i} → suc i < n → R (f (suc i)) (f i)) →
                    AllNeighbours R (applyDownFrom f n)
  applyDownFrom⁺₁ f zero          Rf = []
  applyDownFrom⁺₁ f (suc zero)    Rf = [-]
  applyDownFrom⁺₁ f (suc (suc n)) Rf =
    Rf ≤-refl ∷ applyDownFrom⁺₁ f (suc n) (Rf ∘ ≤-step)

  applyDownFrom⁺₂ : ∀ f n → (∀ i → R (f (suc i)) (f i)) →
                    AllNeighbours R (applyDownFrom f n)
  applyDownFrom⁺₂ f n Rf = applyDownFrom⁺₁ f n (λ _ → Rf _)
