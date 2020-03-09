------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use `Data.Vec.Functional` instead.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Disabled to prevent warnings from other Table modules
{-# OPTIONS --warn=noUserWarning #-}

module Data.Table.Relation.Equality where

open import Data.Table.Relation.Binary.Equality public

{-# WARNING_ON_IMPORT
"Data.Table.Relation.Equality was deprecated in v1.0.
Use Data.Vec.Functional.Relation.Binary.Pointwise instead."
#-}
