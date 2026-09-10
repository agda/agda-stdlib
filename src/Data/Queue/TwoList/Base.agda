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
open import Data.List.Base as List using (List; []; _∷_; [_]; reverse; _++_; length; null)
open import Data.List.Relation.Unary.All using (Null; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (null⇒Null; Null⇒null)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Queue.QueueSpec using (RawQueue; IsQueue)
open import Data.SnocList.Base as SnocList using (List<; toList>; fromList>; []; _<:_; _<><_)
open import Data.SnocList.Relation.Unary.All
open import Data.SnocList.Relation.Unary.All.Properties using (¬null-<:; null-<:→nullxs)
open import Data.Unit.Base using (⊤)
open import Function.Base using (id; const; _∘_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable.Core using (yes; no; isYes; False)
open import Relation.Nullary.Reflects using (ofʸ; ofⁿ)
open import Relation.Unary using (Pred; Decidable)

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
    front : List< A
    back  : List A
    inv : Null< front → Null back

------------------------------------------------------------------------
--- Basic Functions/Relations/Operators

Empty    : ∀ {A : Set a} → Pred (Queue A) a
Empty {a} {A} q = Null< (Queue.front q)

empty? : Decidable (Empty {A = A})
empty? (mkQ front back inv) .Relation.Nullary.does = SnocList.null front
empty? (mkQ [] back inv) .Relation.Nullary.proof = ofʸ []
empty? (mkQ (xs <: x) back inv) .Relation.Nullary.proof = ofⁿ λ null< → contradiction null< ¬null-<:

isEmpty : Queue A → Bool
isEmpty q = SnocList.null (Queue.front q)

------------------------------------------------------------------------
--- Smart Constructor

queue : List< A → List A → Queue A
queue []          ys = mkQ ([] <>< ys) [] (const [])
queue xs@(_ <: _) ys = mkQ xs ys null-<:→nullxs

------------------------------------------------------------------------
--- Conversion to/from List

-- Create a List from a Queue, such that the last that would be dequeued
-- becomes the head of the list
toList : Queue A → List A
toList q = (Queue.back q) ++ (toList> (Queue.front q))

-- Create a Queue from a List, such that the elements
-- of the list would be dequeued starting from its last element
fromList : List A → Queue A
fromList xs = queue [] xs

------------------------------------------------------------------------
-- Construction & Destruction

empty : Queue A
empty = fromList []

enqueue : A → Queue A → Queue A
enqueue x q with bs ← Queue.back q | Queue.front q
... | []            = queue ([] <: x) []
... | front@(_ <: _) = queue front (x ∷ bs)

dequeue : ∀ (q : Queue A) .{{_ : False (empty? q)}} → Queue A × A
dequeue (mkQ (xs <: x) back _) = queue xs back , x

-- Create a queue with a single element
singleton : A → Queue A
singleton = fromList ∘ [_]

-- map : (A → B) → Queue A → Queue B
-- map f empty = empty
-- map f (queue x xs ys) = queue (f x) (List.map f xs) (List.map f ys)

------------------------------------------------------------------------
-- Relations

-- Under the property that toList returns a list in
-- the order of dequeue
_≈_ : ∀ {A : Set a} → Rel (Queue A) a
q ≈ q' = (toList q) ≡ (toList q')

------------------------------------------------------------------------
-- Size

size : Queue A → ℕ
size = length ∘ toList
