------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use Data.Word64 instead
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Word where

open import Data.Word64 public

{-# WARNING_ON_IMPORT
"Data.Word was deprecated in v2.1. Use Data.Word64 instead."
#-}
