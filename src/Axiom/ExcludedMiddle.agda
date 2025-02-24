------------------------------------------------------------------------
-- The Agda standard library
--
-- Results concerning the excluded middle axiom.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Axiom.ExcludedMiddle where

open import Level using (Level; suc)
open import Relation.Nullary.Decidable.Core using (Dec)

------------------------------------------------------------------------
-- Definition

-- The classical statement of excluded middle says that every
-- statement/set is decidable (i.e. it either holds or it doesn't hold).

ExcludedMiddle : ∀ ℓ → Set (suc ℓ)
ExcludedMiddle ℓ = {P : Set ℓ} → Dec P
