------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for reasoning with a partial setoid
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (PartialSetoid)
open import Relation.Binary.Reasoning.Syntax

module Relation.Binary.Reasoning.PartialSetoid
  {s₁ s₂} (S : PartialSetoid s₁ s₂) where

open PartialSetoid S

import Relation.Binary.Reasoning.Base.Partial _≈_ trans
  as ≈-Reasoning

------------------------------------------------------------------------
-- Reasoning combinators

-- Export the combinators for partial relation reasoning, hiding the
-- single misnamed combinator.
open ≈-Reasoning public hiding (step-∼)

-- Re-export the equality-based combinators instead
open ≈-syntax _IsRelatedTo_ _IsRelatedTo_ ≈-Reasoning.∼-go sym public
