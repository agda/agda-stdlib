------------------------------------------------------------------------
-- The Agda standard library
--
-- Freely adding a Point to any Set
------------------------------------------------------------------------

module Relation.Binary.Construction.Pointed where

open import Data.Maybe
  renaming (Maybe to Pointed; nothing to ∙; just to [_]; just-injective to []-injective)
  using ()
  public
