------------------------------------------------------------------------
-- The Agda standard library
--
-- Slices in the propositional sublist category.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Sublist.Propositional.Slice
  {a} {A : Set a} where

open import Data.List.Base using (List)
open import Data.List.Relation.Binary.Sublist.Propositional
 using (_⊆_; UpperBound; ⊆-trans; ∷ₙ-ub; _∷ʳ_; _∷ₗ-ub_; _∷_; _∷ᵣ-ub_;
        _,_∷-ub_; ⊆-upper-bound; [])
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong)

------------------------------------------------------------------------
-- A Union where the triangles commute is a
-- Cospan in the slice category (_ ⊆ zs).

record IsCospan {xs ys zs : List A} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} (u : UpperBound τ₁ τ₂) : Set a where
  field
    tri₁ : ⊆-trans (UpperBound.inj₁ u) (UpperBound.sub u) ≡ τ₁
    tri₂ : ⊆-trans (UpperBound.inj₂ u) (UpperBound.sub u) ≡ τ₂

record Cospan {xs ys zs : List A} (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs) : Set a where
  field
    upperBound : UpperBound τ₁ τ₂
    isCospan   : IsCospan upperBound

  open UpperBound upperBound public
  open IsCospan isCospan public

open IsCospan
open Cospan

module _
  {x : A} {xs ys zs : List A} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs}
  {u : UpperBound τ₁ τ₂} (c : IsCospan u) where
  open UpperBound u
  open IsCospan c

  ∷ₙ-cospan : IsCospan (∷ₙ-ub u)
  ∷ₙ-cospan = record
    { tri₁ = cong (x ∷ʳ_) (c .tri₁)
    ; tri₂ = cong (x ∷ʳ_) (c .tri₂)
    }

  ∷ₗ-cospan : IsCospan (refl {x = x} ∷ₗ-ub u)
  ∷ₗ-cospan = record
    { tri₁ = cong (refl ∷_) (c .tri₁)
    ; tri₂ = cong (x   ∷ʳ_) (c .tri₂)
    }

  ∷ᵣ-cospan : IsCospan (refl {x = x} ∷ᵣ-ub u)
  ∷ᵣ-cospan = record
    { tri₁ = cong (x   ∷ʳ_) (c .tri₁)
    ; tri₂ = cong (refl ∷_) (c .tri₂)
    }

  ∷-cospan : IsCospan (refl {x = x} , refl {x = x} ∷-ub u)
  ∷-cospan = record
   { tri₁ =  cong (refl ∷_) (c .tri₁)
   ; tri₂ =  cong (refl ∷_) (c .tri₂)
   }

⊆-upper-bound-is-cospan : ∀ {xs ys zs : List A} (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs) →
  IsCospan (⊆-upper-bound τ₁ τ₂)
⊆-upper-bound-is-cospan [] [] = record { tri₁ = refl ; tri₂ = refl }
⊆-upper-bound-is-cospan (z   ∷ʳ τ₁) (.z  ∷ʳ τ₂) = ∷ₙ-cospan (⊆-upper-bound-is-cospan τ₁ τ₂)
⊆-upper-bound-is-cospan (z   ∷ʳ τ₁) (refl ∷ τ₂) = ∷ᵣ-cospan (⊆-upper-bound-is-cospan τ₁ τ₂)
⊆-upper-bound-is-cospan (refl ∷ τ₁) (z   ∷ʳ τ₂) = ∷ₗ-cospan (⊆-upper-bound-is-cospan τ₁ τ₂)
⊆-upper-bound-is-cospan (refl ∷ τ₁) (refl ∷ τ₂) = ∷-cospan (⊆-upper-bound-is-cospan τ₁ τ₂)

⊆-upper-bound-cospan : ∀ {xs ys zs : List A} (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs) →
  Cospan τ₁ τ₂
⊆-upper-bound-cospan τ₁ τ₂ = record
  { upperBound = ⊆-upper-bound τ₁ τ₂
  ; isCospan   = ⊆-upper-bound-is-cospan τ₁ τ₂
  }
