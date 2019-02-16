------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic products of binary relations
--
-- This module is DEPRECATED. Please use
-- Data.Product.Binary.Relation.Lex.Strict directly.
------------------------------------------------------------------------

-- The definition of lexicographic product used here is suitable if
-- the left-hand relation is a strict partial order.

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Product.StrictLex where

open import Data.Product.Relation.Binary.Lex.Strict public
