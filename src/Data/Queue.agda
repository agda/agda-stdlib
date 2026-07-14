------------------------------------------------------------------------
-- The Agda standard library
--
-- Functional queues (two-list representation)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Queue where

open import Level using (Level)
open import Data.List.Base as List using (List; []; _∷_; reverse; _++_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Definition
--
-- A queue is represented as a pair (front , back) where:
--   - front is the front of the queue (first to be dequeued)
--   - back  is the back in reverse order (last element at head)
--
-- Invariant: front is empty only when the whole queue is empty.

record Queue (A : Set a) : Set a where
  constructor mkQueue
  field
    front : List A
    back  : List A

------------------------------------------------------------------------
-- Construction

empty : Queue A
empty = mkQueue [] []

-- Re-balance: move reversed back to front when front is exhausted.
private
  balance : List A → List A → Queue A
  balance []       back = mkQueue (reverse back) []
  balance (x ∷ xs) back = mkQueue (x ∷ xs) back

enqueue : A → Queue A → Queue A
enqueue x (mkQueue f b) = balance f (x ∷ b)

------------------------------------------------------------------------
-- Deconstruction

dequeue : Queue A → Maybe (A × Queue A)
dequeue (mkQueue []       _) = nothing
dequeue (mkQueue (x ∷ xs) b) = just (x , balance xs b)

------------------------------------------------------------------------
-- Queries

isEmpty : Queue A → Bool where
  open import Data.Bool.Base using (Bool; true; false)
isEmpty (mkQueue [] _) = true
isEmpty _              = false

size : Queue A → ℕ
size (mkQueue f b) = List.length f + List.length b

------------------------------------------------------------------------
-- Conversion

toList : Queue A → List A
toList (mkQueue f b) = f ++ reverse b

fromList : List A → Queue A
fromList []       = empty
fromList (x ∷ xs) = enqueue x (fromList xs)
