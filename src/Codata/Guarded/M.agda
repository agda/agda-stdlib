------------------------------------------------------------------------
-- The Agda standard library
--
-- M-types (the dual of W-types)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe --guardedness #-}

module Codata.Guarded.M where

open import Level
open import Data.Container.Core hiding (map; Shape; Position)
open import Function.Base
open import Data.Product hiding (map)

-- The family of M-types

record M {s p} (C : Container s p) : Set (s ⊔ p) where
  coinductive
  constructor inf

  open Container C

  field
    head : Shape
    tail : Position head → M C

open M public

-- map

module _ {s₁ s₂ p₁ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂}
         (f : C₁ ⇒ C₂) where

  map : M C₁ → M C₂
  map m .head = f .shape (m .head)
  map m .tail p = map (m .tail (f .position p))

-- unfold

module _ {s p ℓ} {C : Container s p} (open Container C)
         {S : Set ℓ} (alg : S → ⟦ C ⟧ S) where

  unfold : S → M C
  unfold seed .head = alg seed .proj₁
  unfold seed .tail p = unfold (alg seed .proj₂ p)
