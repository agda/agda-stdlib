------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of algebraic structures like semilattices and lattices
-- (packed in records together with sets, operations, etc.), defined via
-- meet/join operations and their properties
--
-- For lattices defined via an order relation, see
-- Relation.Binary.Lattice.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Lattice where

open import Algebra.Lattice.Structures public
open import Algebra.Lattice.Structures.Biased public
open import Algebra.Lattice.Bundles public
