------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic products of binary relations
--
-- This module is DEPRECATED. Please use
-- Data.Product.Relation.Lex.NonStrict directly.
------------------------------------------------------------------------

-- The definition of lexicographic product used here is suitable if
-- the left-hand relation is a (non-strict) partial order.

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Product.NonStrictLex where

open import Data.Product.Relation.Lex.NonStrict public
