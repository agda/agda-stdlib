------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
--
-- Please use Data.Vec.Relation.Pointwise.Inductive
-- and Data.Vec.Relation.Pointwise.Extensional directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Vec.Pointwise where

open import Data.Vec.Relation.Pointwise.Inductive public
  hiding (head; tail)
open import Data.Vec.Relation.Pointwise.Extensional public
  using (head; tail) renaming (Pointwise to Pointwise′)
