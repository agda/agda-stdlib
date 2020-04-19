------------------------------------------------------------------------
-- The Agda standard library
--
-- Universal lifting of predicates over Vectors
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Functional.Relation.Unary.All where

open import Data.Fin.Base
open import Data.Fin.Properties
open import Data.Nat.Base
open import Data.Product using (_,_)
open import Data.Vec.Functional as VF hiding (map)
open import Level using (Level)
open import Relation.Unary

private
  variable
    a p q ℓ : Level
    A : Set a

------------------------------------------------------------------------
-- Definition

All : Pred A ℓ → ∀ {n} → Vector A n → Set ℓ
All P xs = ∀ i → P (xs i)

------------------------------------------------------------------------
-- Operations

module _ {P : Pred A p} {Q : Pred A q} where

  map : P ⊆ Q → ∀ {n} → All P {n = n} ⊆ All Q
  map p⊆q ps i = p⊆q (ps i)

------------------------------------------------------------------------
-- Properties of predicates preserved by All

module _ {P : Pred A p} where

  all : Decidable P → ∀ {n} → Decidable (All P {n = n})
  all p? xs = all? λ i → p? (xs i)

  universal : Universal P → ∀ {n} → Universal (All P {n = n})
  universal uni xs i = uni (xs i)

  satisfiable : Satisfiable P → ∀ {n} → Satisfiable (All P {n = n})
  satisfiable (x , px) = (λ _ → x) , (λ _ → px)
