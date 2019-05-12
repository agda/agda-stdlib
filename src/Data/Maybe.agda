------------------------------------------------------------------------
-- The Agda standard library
--
-- The Maybe type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Maybe where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Bool.Base using (T)
open import Data.Maybe.Relation.Unary.All
open import Data.Maybe.Relation.Unary.Any
open import Level using (Level)

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- The base type and some operations

open import Data.Maybe.Base public

------------------------------------------------------------------------
-- Using Any and All to define Is-just and Is-nothing

Is-just : Maybe A → Set _
Is-just = Any (λ _ → ⊤)

Is-nothing : Maybe A → Set _
Is-nothing = All (λ _ → ⊥)

to-witness : ∀ {m : Maybe A} → Is-just m → A
to-witness (just {x = p} _) = p

to-witness-T : ∀ (m : Maybe A) → T (is-just m) → A
to-witness-T (just p) _  = p
