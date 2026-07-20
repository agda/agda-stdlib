------------------------------------------------------------------------
-- The Agda standard library
--
-- Queues, basic types and operations
------------------------------------------------------------------------
{-# OPTIONS --without-K --safe #-}

-- Queues implemented with the usual two-list method

module Data.Queue.Base where

open import Agda.Builtin.Equality
open import Level using (Level)
open import Data.Bool
open import Data.List.Base as List using (List; []; _∷_; reverse; _++_; length)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Function

private
  variable
    l : Level
    A B : Set l

-- A Queue consists of a dequeue and enqueue list
-- When enqueing (unless it is the first element), elements are cons'd
-- to the enqueue list.
--
-- When dequeuing, elements are taken from the head of the dequeue
-- list. If this is empty, the enqueue list is reversed and swapped
-- with the dequeue list.
--
-- The dequeue-list should be empty iff the whole queue is empty.
-- To enforce this, the head of the dequeue list is taken
-- seperately and a constructor for an empty queue is given.

data Queue (A : Set l) : Set l where
  empty : Queue A
  
  -- dequeue-head → dequeue-list → enqueue-list
  queue : A → List A → List A → Queue A

------------------------------------------------------------------------
-- Construction & Destruction

enqueue : Queue A → A → Queue A
enqueue empty a = queue a [] []  
enqueue (queue dq-hd dq-tail eq) a = queue dq-hd dq-tail (a ∷ eq)

-- Create a queue with a single element
singleton : A → Queue A
singleton = enqueue empty

dequeue : Queue A → Maybe (A × Queue A)
dequeue empty = nothing
dequeue (queue dq-hd [] eq) with reverse eq
... | [] = just (dq-hd , empty)
... | x ∷ req = just (dq-hd , queue x req [])
dequeue (queue dq-hd (x ∷ xs) eq) = just (dq-hd , (queue x xs eq))

------------------------------------------------------------------------
--- Basic Functions

isEmpty : Queue A → Bool
isEmpty empty = true
isEmpty _ = false

size : Queue A → ℕ
size empty = 0
size (queue x xs ys) = 1 + length xs + length ys

map : (A → B) → Queue A → Queue B
map f empty = empty
map f (queue x xs ys) = queue (f x) (List.map f xs) (List.map f ys)

------------------------------------------------------------------------
--- Conversion to/from List

-- Create a List from a Queue, such that the first that would be dequeued
-- becomes the head of the list (i.e. the first element of the queue
-- becomes the last element of the list)
toList : Queue A → List A
toList empty = []
toList (queue dq-hd dq-tail eq) = dq-hd ∷ (dq-tail ++ (reverse eq))

-- Create a Queue from a List, such that the elements
-- of the list would be dequeued starting from its first element
-- (i.e. the first element of the list becomes the last element of the queue)
fromList : List A → Queue A
fromList [] = empty
fromList (x ∷ xs) = queue x xs []
