------------------------------------------------------------------------
-- The Agda standard library
--
-- An either-or-both data type
------------------------------------------------------------------------

module Data.These where

open import Data.These.Base public
open import Data.Maybe.Base
open import Function

module _ {a b} {A : Set a} {B : Set b} where

-- Deletion

  deleteThis : These A B → Maybe (These A B)
  deleteThis = fold (const nothing) (just ∘′ that) (const (just ∘′ that))

  deleteThat : These A B → Maybe (These A B)
  deleteThat = fold (just ∘′ this) (const nothing) (const ∘′ just ∘′ this)

-- Component extraction via Maybe

  fromThis : These A B → Maybe A
  fromThis = fold just (const nothing) (const ∘′ just)

  fromThat : These A B → Maybe B
  fromThat = fold (const nothing) just (const just)
