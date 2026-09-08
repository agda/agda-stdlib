------------------------------------------------------------------------
-- The Agda standard library
--
-- Notation for adding an additional point to any set
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Construct.Add.Point where

open import Data.Maybe.Base public
  using () renaming (Maybe to Pointed; nothing to ∙; just to [_])

open import Data.Maybe.Properties public
  using (≡-dec) renaming (just-injective to []-injective)
