------------------------------------------------------------------------
-- The Agda standard library
--
-- An either-or-both data type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.These where

open import Level
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Sum.Base using (_⊎_; [_,_]′)
open import Function


------------------------------------------------------------------------
-- Re-exporting the datatype and its operations

open import Data.These.Base public

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Additional operations

-- projections

fromThis : These A B → Maybe A
fromThis = fold just (const nothing) (const ∘′ just)

fromThat : These A B → Maybe B
fromThat = fold (const nothing) just (const just)

leftMost : These A A → A
leftMost = fold id id const

rightMost : These A A → A
rightMost = fold id id (flip const)

mergeThese : (A → A → A) → These A A → A
mergeThese = fold id id

-- deletions

deleteThis : These A B → Maybe (These A B)
deleteThis = fold (const nothing) (just ∘′ that) (const (just ∘′ that))

deleteThat : These A B → Maybe (These A B)
deleteThat = fold (just ∘′ this) (const nothing) (const ∘′ just ∘′ this)
