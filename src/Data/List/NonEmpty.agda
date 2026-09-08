------------------------------------------------------------------------
-- The Agda standard library
--
-- Non-empty lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.NonEmpty where

open import Level using (Level)
open import Data.List.Base as List using (List)

------------------------------------------------------------------------
-- Re-export basic type and operations

open import Data.List.NonEmpty.Base public
