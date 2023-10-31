------------------------------------------------------------------------
-- The Agda standard library
--
-- This module collects the property definitions for left-scaling
-- (LeftDefs), right-scaling (RightDefs), and both (BiDefs).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Module.Definitions where

  import Algebra.Module.Definitions.Left as L
  import Algebra.Module.Definitions.Right as R
  import Algebra.Module.Definitions.Bi as B
  import Algebra.Module.Definitions.Bi.Simultaneous as BS

  module LeftDefs = L
  module RightDefs = R
  module BiDefs = B
  module SimultaneousBiDefs = BS
