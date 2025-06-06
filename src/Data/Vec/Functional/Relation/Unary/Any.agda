------------------------------------------------------------------------
-- The Agda standard library
--
-- Existential lifting of predicates over Vectors
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Functional.Relation.Unary.Any where

open import Data.Fin.Base using (zero; suc)
open import Data.Fin.Properties using (any?)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base as Σ using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Functional as VF hiding (map)
open import Function.Base using (id)
open import Level using (Level)
open import Relation.Unary using (Pred; _⊆_; Decidable)

private
  variable
    a b p q ℓ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definition

Any : Pred A ℓ → ∀ {n} → Vector A n → Set ℓ
Any P xs = ∃ λ i → P (xs i)

------------------------------------------------------------------------
-- Operations

module _ {P : Pred A p} where

  here : ∀ {x n} {v : Vector A n} → P x → Any P (x ∷ v)
  here px = zero , px

  there : ∀ {x n} {v : Vector A n} → Any P v → Any P (x ∷ v)
  there = Σ.map suc id

module _ {P : Pred A p} {Q : Pred A q} where

  map : P ⊆ Q → ∀ {n} → Any P {n = n} ⊆ Any Q
  map p⊆q = Σ.map id p⊆q

------------------------------------------------------------------------
-- Properties of predicates preserved by Any

module _ {P : Pred A p} where

  any : Decidable P → ∀ {n} → Decidable (Any P {n = n})
  any p? xs = any? λ i → p? (xs i)
