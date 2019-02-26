------------------------------------------------------------------------
-- The Agda standard library
--
-- Notation for adding an additional point to any set
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Construct.Add.Point where

open import Data.Maybe.Base using ()
  renaming (Maybe to Pointed; nothing to ∙; just to [_])
  public
