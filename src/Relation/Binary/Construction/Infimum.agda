------------------------------------------------------------------------
-- The Agda standard library
--
-- Freely adding an Infimum to any Set
------------------------------------------------------------------------

module Relation.Binary.Construction.Infimum where

open import Data.Maybe.Base
  renaming (Maybe to _₋; nothing to ⊥⁺; just to [_])
  using ()
  public
