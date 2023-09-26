------------------------------------------------------------------------
-- The Agda standard library
--
-- Characters
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Char where

------------------------------------------------------------------------
-- Re-export base definitions and decidability of equality

open import Data.Char.Base public
open import Data.Char.Properties
  using (_≈?_; _≟_; _<?_; _≤?_; _==_) public
