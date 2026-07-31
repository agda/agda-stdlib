------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances of TwoLisQueue
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Queue.TwoList.Instances where

open import Data.Queue.TwoList.Base
open import Data.Queue.QueueSpec using (RawQueue)
open import Level using (Level)

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
--- TwoList Queue is a Queue

instance
  TwoList-RawQueue : RawQueue {a} Queue
  TwoList-RawQueue = record
    { _≈_      = _≈_
    ; Empty    = Empty
    ; empty?   = empty?
    ; fromList = fromList
    ; toList   = toList
    ; enqueue  = enqueue
    ; dequeue  = dequeue
    }
