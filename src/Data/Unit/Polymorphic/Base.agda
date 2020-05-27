------------------------------------------------------------------------
-- The Agda standard library
--
-- A universe polymorphic unit type, as a Lift of the Level 0 one.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Unit.Polymorphic.Base where

open import Level
import Data.Unit.Base as ⊤

------------------------------------------------------------------------
-- A unit type defined as a synonym

⊤ : {ℓ : Level} → Set ℓ
⊤ {ℓ} = Lift ℓ ⊤.⊤

tt : {ℓ : Level} → ⊤ {ℓ}
tt = lift ⊤.tt
