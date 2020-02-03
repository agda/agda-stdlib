------------------------------------------------------------------------
-- The Agda standard library
--
-- This module collects the property definitions for left-scaling
-- (LeftDefs), right-scaling (RightDefs), and both (BiDefs).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Algebra.Module.Definitions where

  open import Algebra.Core

  import Algebra.Module.Definitions.Left as L
  import Algebra.Module.Definitions.Right as R
  import Algebra.Module.Definitions.Bi as B

  module LeftDefs = L
  module RightDefs = R
  module BiDefs = B
