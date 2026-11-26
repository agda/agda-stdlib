------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances of TwoList Queue
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Queue.TwoList.Instances where

open import Data.Queue.TwoList.Base
open import Data.Queue.TwoList.Properties
open import Data.Queue.QueueSpec using (RawQueue; IsQueue)
open import Level using (Level)

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
--- TwoList Queue is a Raw Queue

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
    ; size     = size
    }

------------------------------------------------------------------------
-- TwoList Queue is a Queue!

-- NOTE: for some reason, unless manually passing some implicits, other implicits remain
-- unsolved? This is also means that you can't assign fields with record syntax and
-- have to use co-pattern matching. My knowledge of implicits isn't good enough to know
-- why or if this indicates 'bad ergonomics'

instance
  TwoList-IsQueue : IsQueue {a} Queue
  TwoList-IsQueue .IsQueue.rawQ = TwoList-RawQueue
  TwoList-IsQueue .IsQueue.isEquivalence = ≈-isEquivalence
  TwoList-IsQueue .IsQueue.≈-resp-Empty {x = x} {y} = ≈-resp-Empty {x = x} {y = y}
  TwoList-IsQueue .IsQueue.≈-=[toList]⇒-≡ {x = x} {y} = ≈-=[toList]⇒-≡ {x = x} {y = y}
  TwoList-IsQueue .IsQueue.empty-toList {q = q} = empty-toList {q = q}
  TwoList-IsQueue .IsQueue.empty-fromList = empty-fromList
  TwoList-IsQueue .IsQueue.toList-fromList {q = q} = toList-fromList {q = q}
  TwoList-IsQueue .IsQueue.fromList-toList {q = q} = fromList-toList {q = q}
  TwoList-IsQueue .IsQueue.toList-enqueue {q = q} = toList-enqueue {q = q}
  TwoList-IsQueue .IsQueue.toList-dequeue {q = q} = toList-dequeue {q = q}
