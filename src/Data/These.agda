------------------------------------------------------------------------
-- The Agda standard library
--
-- An either-or-both data type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.These where

open import Data.These.Base public
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Sum.Base using (_⊎_; [_,_]′)
open import Function

module _ {a b} {A : Set a} {B : Set b} where

------------------------------------------------------------------------
-- Sum-related functions

  fromSum : A ⊎ B → These A B
  fromSum = [ this , that ]′

------------------------------------------------------------------------
-- Maybe-related functions

-- Deletions.
  deleteThis : These A B → Maybe (These A B)
  deleteThis = fold (const nothing) (just ∘′ that) (const (just ∘′ that))

  deleteThat : These A B → Maybe (These A B)
  deleteThat = fold (just ∘′ this) (const nothing) (const ∘′ just ∘′ this)

-- Injections.
  thisM : A → Maybe B → These A B
  thisM a = maybe′ (these a) (this a)

  thatM : Maybe A → B → These A B
  thatM = maybe′ these that

-- Projections.
  fromThis : These A B → Maybe A
  fromThis = fold just (const nothing) (const ∘′ just)

  fromThat : These A B → Maybe B
  fromThat = fold (const nothing) just (const just)
