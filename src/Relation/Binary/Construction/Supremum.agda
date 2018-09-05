------------------------------------------------------------------------
-- The Agda standard library
--
-- Freely adding a Supremum to any Set
------------------------------------------------------------------------

module Relation.Binary.Construction.Supremum where

open import Relation.Binary.Construction.Pointed
  renaming (Pointed to _⁺; ∙ to ⊤⁺)
  public
