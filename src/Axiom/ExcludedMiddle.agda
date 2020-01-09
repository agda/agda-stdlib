------------------------------------------------------------------------
-- The Agda standard library
--
-- Results concerning the excluded middle axiom.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Axiom.ExcludedMiddle where

open import Level
open import Relation.Nullary

------------------------------------------------------------------------
-- Definition

-- The classical statement of excluded middle says that every
-- statement/set is decidable (i.e. it either holds or it doesn't hold).

ExcludedMiddle : (ℓ : Level) → Set (suc ℓ)
ExcludedMiddle ℓ = {P : Set ℓ} → Dec P
