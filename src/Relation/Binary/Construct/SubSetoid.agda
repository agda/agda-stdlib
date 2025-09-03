------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversion of a PartialSetoid into a Setoid
------------------------------------------------------------------------

open import Relation.Binary.Bundles using (PartialSetoid)

module Relation.Binary.Construct.SubSetoid
  {a ℓ} (S : PartialSetoid a ℓ)
  where

open import Function.Base using (id)
import Relation.Binary.Construct.Kernel as Kernel


------------------------------------------------------------------------
-- Definitions

open module SubSetoid = Kernel S id id public
