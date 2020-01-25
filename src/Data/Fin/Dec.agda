------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use the Data.Fin.Properties
-- and Data.Fin.Subset.Properties directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Dec where

open import Data.Fin.Properties public
  using (decFinSubset; any?; all?; ¬∀⟶∃¬-smallest; ¬∀⟶∃¬)

open import Data.Fin.Subset.Properties public
  using (_∈?_; _⊆?_; nonempty?; anySubset?)
  renaming (Lift? to decLift)

{-# WARNING_ON_IMPORT
"Data.Fin.Dec was deprecated in v0.17.
Use Data.Fin.Properties and Data.Fin.Subset.Properties instead."
#-}
