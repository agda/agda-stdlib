------------------------------------------------------------------------
-- The Agda standard library
--
-- Many properties which hold for `∼` also hold for `flip ∼`. Unlike
-- the module `Relation.Binary.Construct.Flip` this module does not
-- flip the underlying equality.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Construct.Converse where

open import Relation.Binary.Construct.Flip.EqAndOrd public

{-# WARNING_ON_IMPORT
"Relation.Binary.Construct.Converse was deprecated in v2.0.
Use Relation.Binary.Construct.Flip.EqAndOrd instead."
#-}
