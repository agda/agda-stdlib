------------------------------------------------------------------------
-- The Agda standard library
--
-- Existence of an index at which a predicate holds
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Functional.Relation.Unary.Any where

open import Data.Fin
open import Data.Fin.Properties
open import Data.Nat
open import Data.Product as Σ using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Functional as VF hiding (map)
open import Function
open import Level using (Level)
open import Relation.Unary

private
  variable
    a b p q ℓ : Level
    A : Set a
    B : Set b
    P : Pred A p
    Q : Pred A q
    m n : ℕ

------------------------------------------------------------------------
-- Definition

Any : Pred A ℓ → Vector A n → Set ℓ
Any P u = ∃ \ i → P (u i)

------------------------------------------------------------------------
-- Operations

map : P ⊆ Q → Any {n = n} P ⊆ Any Q
map f = Σ.map id f

here : ∀ {x} {v : Vector A n} → P x → Any P (x ∷ v)
here px = zero , px

there : ∀ {x} {v : Vector A n} → Any P v → Any P (x ∷ v)
there = Σ.map suc id

------------------------------------------------------------------------
-- Properties of predicates preserved by Any

any : Decidable P → Decidable (Any {n = n} P)
any p? u = any? \ i → p? (u i)
