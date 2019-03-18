------------------------------------------------------------------------
-- The Agda standard library
--
-- Characters
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Char where

------------------------------------------------------------------------
-- Re-export base definitions and decidability of equality

open import Data.Char.Base public
open import Data.Char.Properties using (_≟_; _==_) public
