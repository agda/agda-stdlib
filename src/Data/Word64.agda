------------------------------------------------------------------------
-- The Agda standard library
--
-- Machine words
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Word64 where

------------------------------------------------------------------------
-- Re-export base definitions and decidability of equality

open import Data.Word64.Base public
open import Data.Word64.Properties using (_≈?_; _<?_; _≟_; _==_) public
