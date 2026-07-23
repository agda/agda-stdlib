------------------------------------------------------------------------
-- The Agda standard library
--
-- Queue specification
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Queue.QueueSpec where

open import Data.List.Base using (List)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_)
open import Level using (Level)

private
  variable
    a b : Level
    A : Set a
    B : Set b

-- Along these lines?
record IsQueue (Queue : (Set a) → (Set a)) : (Set (Level.suc a)) where
  field
    enqueue : A → Queue A → Queue A
    dequeue : Queue A → Maybe (A × Queue A)

    empty : Queue A
    size : Queue A → ℕ

    toList : Queue A → List A
    fromList : List A → Queue A
