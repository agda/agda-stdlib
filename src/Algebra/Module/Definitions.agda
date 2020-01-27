------------------------------------------------------------------------
-- The Agda standard library
--
-- TODO: description
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

-- The properties are parameterised by the two carriers and
-- the result equality.

module Algebra.Module.Definitions where

  open import Algebra.Core

  import Algebra.Module.Definitions.Left as L
  import Algebra.Module.Definitions.Right as R
  import Algebra.Module.Definitions.Bi as B

  module LeftDefs = L
  module RightDefs = R
  module BiDefs = B
