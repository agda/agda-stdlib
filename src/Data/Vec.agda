------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors
------------------------------------------------------------------------

-- This implementation is designed for reasoning about dynamic
-- vectors which may increase or decrease in size.

-- See `Data.Vec.Functional` for an alternative implementation as
-- functions from finite sets, which is more suitable for reasoning
-- about fixed sized vectors and for when ease of retrevial is
-- important.

{-# OPTIONS --without-K --safe #-}

module Data.Vec where

open import Level
open import Data.Bool.Base
open import Data.List.Base as List using (List)
import Data.Nat.Properties as ℕₚ
open import Data.Product as Prod using (∃)
open import Data.Vec.Bounded.Base as Vec≤
  using (Vec≤; ≤-cast; fromVec)
open import Function.Base
open import Relation.Nullary
open import Relation.Unary

private
  variable
    a p : Level
    A : Set a

------------------------------------------------------------------------
-- Publicly re-export the contents of the base module

open import Data.Vec.Base public

------------------------------------------------------------------------
-- Additional operations

module _ {P : A → Set p} (P? : Decidable P) where

  filter : ∀ {n} → Vec A n → Vec≤ A n
  filter []       = Vec≤.[]
  filter (a ∷ as) with does (P? a)
  ... | true  = a Vec≤.∷ filter as
  ... | false = ≤-cast (ℕₚ.n≤1+n _) (filter as)

  takeWhile : ∀ {n} → Vec A n → Vec≤ A n
  takeWhile []       = Vec≤.[]
  takeWhile (a ∷ as) with does (P? a)
  ... | true  = a Vec≤.∷ takeWhile as
  ... | false = Vec≤.[]

  dropWhile : ∀ {n} → Vec A n → Vec≤ A n
  dropWhile Vec.[]       = Vec≤.[]
  dropWhile (a Vec.∷ as) with does (P? a)
  ... | true  = ≤-cast (ℕₚ.n≤1+n _) (dropWhile as)
  ... | false = fromVec (a Vec.∷ as)

------------------------------------------------------------------------
-- Padding a list of vectors

rectangle : ∀[ Vec≤ A ⇒ Vec A ] → List (∃ (Vec A)) → ∃ (List ∘ Vec A)
rectangle f = Prod.map₂ (List.map f)
            ∘ Vec≤.rectangle
            ∘ List.map (Prod.map₂ fromVec)

rectangleˡ : A → List (∃ (Vec A)) → ∃ (List ∘ Vec A)
rectangleˡ a = rectangle (Vec≤.padLeft a)

rectangleʳ : A → List (∃ (Vec A)) → ∃ (List ∘ Vec A)
rectangleʳ a = rectangle (Vec≤.padRight a)

rectangleᶜ : A → A → List (∃ (Vec A)) → ∃ (List ∘ Vec A)
rectangleᶜ aₗ aᵣ = rectangle (Vec≤.padBoth aₗ aᵣ)
