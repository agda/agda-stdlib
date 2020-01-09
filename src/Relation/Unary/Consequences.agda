------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties imply others
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Unary.Consequences where

open import Relation.Unary
open import Relation.Nullary using (recompute)

dec⟶recomputable : {a ℓ : _} {A : Set a} {P : Pred A ℓ} → Decidable P → Recomputable P
dec⟶recomputable P-dec = recompute (P-dec _)
