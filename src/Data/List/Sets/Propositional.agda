------------------------------------------------------------------------
-- The Agda standard library
--
-- The set interface over propositional equality.
------------------------------------------------------------------------

module Data.List.Sets.Propositional {a} {A : Set a} where

import Data.List.Sets.Setoid as Sets
open import Relation.Binary.PropositionalEquality using (setoid) public

open Sets (setoid A) public
