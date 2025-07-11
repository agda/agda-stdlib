------------------------------------------------------------------------
-- The Agda standard library
--
-- Shim for lemmas re-exported from Algebra.Properties.IsGroup
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles

module Algebra.Properties.Group {g₁ g₂} (G : Group g₁ g₂) where

open Group G using (isGroup)
open import Algebra.Properties.IsGroup isGroup public
