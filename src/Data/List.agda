------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists
------------------------------------------------------------------------

-- See README.Data.List for examples of how to use and reason about
-- lists.

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --warn=noUserWarning #-} -- for deprecated scans etc.

module Data.List where

------------------------------------------------------------------------
-- Types and basic operations

open import Data.List.Base public
  hiding (scanr; scanl)
open import Data.List.Scans public
  using (scanr; scanl)
