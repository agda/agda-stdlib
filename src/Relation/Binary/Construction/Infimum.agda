------------------------------------------------------------------------
-- The Agda standard library
--
-- Freely adding an Infimum to any Set
------------------------------------------------------------------------

module Relation.Binary.Construction.Infimum where

open import Data.Maybe
  renaming (Maybe to _₋; nothing to ⊥⁺; just to [_]; just-injective to [_]-injective)
  using ()
  public
