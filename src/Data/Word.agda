------------------------------------------------------------------------
-- The Agda standard library
--
-- Machine words
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Word where

------------------------------------------------------------------------
-- Re-export base definitions and decidability of equality

open import Data.Word.Base public
open import Data.Word.Properties using (_≈?_; _<?_; _≟_; _==_) public
