------------------------------------------------------------------------
-- The Agda standard library
--
-- The binary relation defined by a constant
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Construct.Constant.Core where

open import Level
open import Relation.Binary.Core using (REL)

private
  variable
    a b c : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definition

Const : Set c → REL A B c
Const I = λ _ _ → I
