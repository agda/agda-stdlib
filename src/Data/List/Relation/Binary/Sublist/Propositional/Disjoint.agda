------------------------------------------------------------------------
-- The Agda standard library
--
-- Sublist-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Sublist.Propositional.Disjoint
  {a} {A : Set a} where

open import Data.List.Base using (List)
open import Data.List.Relation.Binary.Sublist.Propositional
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

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
  (d : Disjoint τ₁ τ₂) (c : IsCospan (⊆-disjoint-union d)) where

  ∷ₙ-cospan : IsCospan (⊆-disjoint-union (x ∷ₙ d))
  ∷ₙ-cospan = record
    { tri₁ = cong (x ∷ʳ_) (c .tri₁)
    ; tri₂ = cong (x ∷ʳ_) (c .tri₂)
    }

  ∷ₗ-cospan : IsCospan (⊆-disjoint-union (refl {x = x} ∷ₗ d))
  ∷ₗ-cospan = record
    { tri₁ = cong (refl ∷_) (c .tri₁)
    ; tri₂ = cong (x   ∷ʳ_) (c .tri₂)
    }

  ∷ᵣ-cospan : IsCospan (⊆-disjoint-union (refl {x = x} ∷ᵣ d))
  ∷ᵣ-cospan = record
    { tri₁ = cong (x   ∷ʳ_) (c .tri₁)
    ; tri₂ = cong (refl ∷_) (c .tri₂)
    }

⊆-disjoint-union-is-cospan : ∀ {xs ys zs : List A} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} →
  (d : Disjoint τ₁ τ₂) → IsCospan (⊆-disjoint-union d)
⊆-disjoint-union-is-cospan [] = record { tri₁ = refl ; tri₂ = refl }
⊆-disjoint-union-is-cospan (x    ∷ₙ d) = ∷ₙ-cospan d (⊆-disjoint-union-is-cospan d)
⊆-disjoint-union-is-cospan (refl ∷ₗ d) = ∷ₗ-cospan d (⊆-disjoint-union-is-cospan d)
⊆-disjoint-union-is-cospan (refl ∷ᵣ d) = ∷ᵣ-cospan d (⊆-disjoint-union-is-cospan d)

⊆-disjoint-union-cospan : ∀ {xs ys zs : List A} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} →
  Disjoint τ₁ τ₂ → Cospan τ₁ τ₂
⊆-disjoint-union-cospan d = record
  { upperBound = ⊆-disjoint-union d
  ; isCospan   = ⊆-disjoint-union-is-cospan d
  }
