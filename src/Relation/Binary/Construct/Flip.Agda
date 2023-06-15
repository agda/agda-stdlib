------------------------------------------------------------------------
-- The Agda standard library
--
-- Many properties which hold for `∼` also hold for `flip ∼`. Unlike
-- the module `Relation.Binary.Construct.Converse` this module flips
-- both the relation and the underlying equality.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Construct.Flip where

open import Relation.Binary.Construct.Flip.Ord public

{-# WARNING_ON_IMPORT
"Relation.Binary.Construct.Flip was deprecated in v2.0.
Use Relation.Binary.Construct.Flip.Ord instead."
#-}
