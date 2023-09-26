------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- `IO.Effectful` instead.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module IO.Categorical where

open import IO.Effectful public

{-# WARNING_ON_IMPORT
"IO.Categorical was deprecated in v2.0.
Use IO.Effectful instead."
#-}
