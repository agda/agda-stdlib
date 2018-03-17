------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of lists
--
-- This module is DEPRECATED. Please use
-- Data.List.Relation.Lex.NonStrict directly.
------------------------------------------------------------------------

-- The definition of lexicographic ordering used here is suitable if
-- the argument order is a (non-strict) partial order. The
-- lexicographic ordering itself can be either strict or non-strict,
-- depending on the value of a parameter.

module Relation.Binary.List.NonStrictLex where

open import Data.List.Relation.Lex.NonStrict public
  hiding (base; halt; this; next; ¬≤-this; ¬≤-next)
open import Data.List.Relation.Lex.Core public
