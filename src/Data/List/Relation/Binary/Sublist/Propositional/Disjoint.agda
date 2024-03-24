------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
-- Please use `Data.List.Relation.Binary.Sublist.Propositional.Slice`
-- instead.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Sublist.Propositional.Disjoint
  {a} {A : Set a} where

{-# WARNING_ON_IMPORT
"Data.List.Relation.Binary.Sublist.Propositional.Disjoint was deprecated in v2.1.
Use Data.List.Relation.Binary.Sublist.Propositional.Slice instead."
#-}

open import Data.List.Base using (List)
open import Data.List.Relation.Binary.Sublist.Propositional using
  ( _⊆_; _∷_; _∷ʳ_
  ; Disjoint; ⊆-disjoint-union; _∷ₙ_; _∷ₗ_; _∷ᵣ_
  )
import Data.List.Relation.Binary.Sublist.Propositional.Slice as SPSlice
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)

open SPSlice using (⊆-upper-bound-is-cospan; ⊆-upper-bound-cospan)

-- For backward compatibility reexport these:
open SPSlice public using ( IsCospan; Cospan )

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
⊆-disjoint-union-is-cospan {τ₁ = τ₁} {τ₂ = τ₂} _ = ⊆-upper-bound-is-cospan τ₁ τ₂

⊆-disjoint-union-cospan : ∀ {xs ys zs : List A} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} →
  Disjoint τ₁ τ₂ → Cospan τ₁ τ₂
⊆-disjoint-union-cospan {τ₁ = τ₁} {τ₂ = τ₂} _ = ⊆-upper-bound-cospan τ₁ τ₂

{-# WARNING_ON_USAGE ⊆-disjoint-union-is-cospan
"Warning: ⊆-disjoint-union-is-cospan was deprecated in v2.1.
Please use `⊆-upper-bound-is-cospan` from `Data.List.Relation.Binary.Sublist.Propositional.Slice` instead."
#-}

{-# WARNING_ON_USAGE ⊆-disjoint-union-cospan
"Warning: ⊆-disjoint-union-cospan was deprecated in v2.1.
Please use `⊆-upper-bound-cospan` from `Data.List.Relation.Binary.Sublist.Propositional.Slice` instead."
#-}
