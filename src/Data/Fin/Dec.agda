------------------------------------------------------------------------
-- The Agda standard library
--
-- Decision procedures for finite sets and subsets of finite sets
--
-- This module is DEPRECATED. Please use the Data.Fin.Properties
-- and Data.Fin.Subset.Properties directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Fin.Dec where

open import Data.Fin.Properties public
  using (decFinSubset; any?; all?; ¬∀⟶∃¬-smallest; ¬∀⟶∃¬)

open import Data.Fin.Subset.Properties public
  using (_∈?_; _⊆?_; nonempty?; anySubset?)
  renaming (Lift? to decLift)
