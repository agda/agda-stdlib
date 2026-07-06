------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties imply others
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Unary.Consequences where

open import Relation.Unary using (Pred; Recomputable; Decidable)
open import Relation.Nullary.Decidable.Core using (recompute)

dec⇒recomputable : {a ℓ : _} {A : Set a} {P : Pred A ℓ} → Decidable P → Recomputable P
dec⇒recomputable P-dec = recompute (P-dec _)

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

dec⟶recomputable = dec⇒recomputable
{-# WARNING_ON_USAGE dec⟶recomputable
"Warning: dec⟶recomputable was deprecated in v2.0.
Please use dec⇒recomputable instead."
#-}
