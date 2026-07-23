------------------------------------------------------------------------
-- The Agda standard library
--
-- Queues, basic types and operations
------------------------------------------------------------------------
{-# OPTIONS --without-K --safe #-}

-- Queues implemented with the two-list method described in
-- "Purely Functional Data Structures", Chris Okasaki, 1996
--
-- Note that the weaker invariant is used here that only guarantees
-- amortized O(1) when the structure is used non-persistently.

module Data.Queue.TwoList.Base where

open import Level using (Level)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.List.Base as List using (List; []; _∷_; reverse; _++_; length)
open import Data.List.Relation.Unary.All using (Null; [])
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.SnocList.Base using (List<; toList>)
open import Function.Base using (id)
open import Relation.Nullary using (¬_)

private
  variable
    a b : Level
    A : Set a
    B : Set b

-- A Queue consists of a front (dequeue) and back (enqueue) list
-- When enqueing (unless it is the first element), elements are cons'd
-- to the enqueue list.
--
-- When dequeuing, elements are taken from the head of the dequeue
-- list. If this is empty, the enqueue list is reversed and swapped
-- with the dequeue list.
--
-- The dequeue-list should be empty iff the whole queue is empty.

record Queue (A : Set a) : Set a where
  constructor mkQ
  field
    front : List A
    back  : List A
    inv : Null front → Null back

------------------------------------------------------------------------
-- Construction & Destruction

empty : Queue A
empty = mkQ [] [] id

-- NOTE: might not be needed. Could be inlined? Existing lemmas exist?
private
  ¬Null : {a : A} {as : List A} → ¬ (Null (a ∷ as))
  ¬Null (() Data.List.Relation.Unary.All.∷ n)

enqueue : A → Queue A → Queue A
enqueue x (mkQ [] back inv) = record
  { front = x ∷ []
  ; back  = back
  ; inv   = λ _ → inv []
  }
enqueue x (mkQ front@(_ ∷ _) back _) = record
  { front = front
  ; back  = x ∷ back
  ; inv   = λ n → ⊥-elim (¬Null n)
  }

-- Create a queue with a single element
singleton : A → Queue A
singleton x = enqueue x empty

dequeue : Queue A → Maybe (A × Queue A)
dequeue (mkQ [] [] inv) = nothing
dequeue (mkQ [] (x ∷ back) inv) = ⊥-elim (¬Null (inv []))
dequeue (mkQ (x ∷ []) back inv) = just (x , record
  { front = reverse back
  ; back  = []
  ; inv   = λ _ → []
  })
dequeue (mkQ (x ∷ y ∷ front) back inv) = just (x , record
  { front = y ∷ front
  ; back  = back
  ; inv   = λ n → ⊥-elim (¬Null n)
  })

------------------------------------------------------------------------
--- Basic Functions

isEmpty : Queue A → Bool
isEmpty (mkQ [] [] inv) = true
isEmpty _ = false

size : Queue A → ℕ
size q = length (Queue.front q) + length (Queue.back q)

-- map : (A → B) → Queue A → Queue B
-- map f empty = empty
-- map f (queue x xs ys) = queue (f x) (List.map f xs) (List.map f ys)

------------------------------------------------------------------------
--- Conversion to/from List

-- Create a List from a Queue, such that the first that would be dequeued
-- becomes the head of the list (i.e. the first element of the queue
-- becomes the last element of the list)
toList : Queue A → List A
toList q = Queue.front q ++ (reverse (Queue.back q))

-- Create a Queue from a List, such that the elements
-- of the list would be dequeued starting from its first element
-- (i.e. the first element of the list becomes the last element of the queue)
fromList : List A → Queue A
fromList list = mkQ list [] λ _ → []
