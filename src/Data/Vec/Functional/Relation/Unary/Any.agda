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

------------------------------------------------------------------------
-- Definition

Any : Pred A ℓ → ∀ {n} → Vector A n → Set ℓ
Any P xs = ∃ \ i → P (xs i)

------------------------------------------------------------------------
-- Operations

map : {P : Pred A p} {Q : Pred A q} → P ⊆ Q → ∀ {n} → Any P {n = n} ⊆ Any Q
map pq = Σ.map id pq

here : ∀ {P : Pred A p} {x n} {v : Vector A n} → P x → Any P (x ∷ v)
here px = zero , px

there : ∀ {P : Pred A p} {x n} {v : Vector A n} → Any P v → Any P (x ∷ v)
there = Σ.map suc id

------------------------------------------------------------------------
-- Properties of predicates preserved by Any

any : {P : Pred A p} → Decidable P → ∀ {n} → Decidable (Any P {n = n})
any p? xs = any? \ i → p? (xs i)
