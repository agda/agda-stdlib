------------------------------------------------------------------------
-- The Agda standard library
--
-- Shim for lemmas re-exported from Algebra.Properties.IsLoop
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Loop)

module Algebra.Properties.Loop {l₁ l₂} (L : Loop l₁ l₂) where

open Loop L using (isLoop)
open import Algebra.Properties.IsLoop isLoop public
