------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- `Relation.Binary.Lattice.Properties.HeytingAlgebra` instead.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Lattice using (HeytingAlgebra)

module Relation.Binary.Properties.HeytingAlgebra
  {c ℓ₁ ℓ₂} (L : HeytingAlgebra c ℓ₁ ℓ₂) where

open import Relation.Binary.Lattice.Properties.HeytingAlgebra L public

{-# WARNING_ON_IMPORT
"Relation.Binary.Properties.HeytingAlgebra was deprecated in v2.0.
Use Relation.Binary.Lattice.Properties.HeytingAlgebra instead."
#-}
