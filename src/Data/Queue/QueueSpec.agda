------------------------------------------------------------------------
-- The Agda standard library
--
-- Queue specification
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Queue.QueueSpec where

open import Data.Bool.Base using (Bool)
open import Data.List.Base as List using (List; []; length)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_)
open import Function.Base using (_∘_)
open import Level
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Nullary.Decidable.Core using (yes; no; isYes; False; does)
open import Relation.Unary using (Pred; Decidable)

private
  variable
    a b : Level
    A : Set a
    B : Set b

-- RawQueue defines the 'computations' available on Queues
-- without any of the associated proofs that determine its
-- correctness.
record RawQueue (Q : Set a → Set a) : Set (suc a) where

  field
    _≈_      : ∀ {A : Set a} → Rel (Q A) a
    Empty    : ∀ {A : Set a} → Pred (Q A) a
    empty?   : Decidable (Empty {A = A})
    fromList : List A → Q A
    toList   : Q A → List A
    enqueue  : A → Q A → Q A
    dequeue  : (q : Q A) → .{{False (empty? q)}} → A × Q A

  empty : Q A
  empty = fromList []

  pure    : A → Q A
  pure = fromList ∘ List.[_]

  toℕ : Q A → ℕ
  toℕ = length ∘ toList

  to𝔹 : Q A → Bool
  to𝔹 = isYes ∘ empty?

  dequeue′ : Q A → Maybe (A × Q A)
  dequeue′ q with empty? q in eq
  ... | yes _ = nothing
  ... | no _  = just (dequeue q)
    where instance
    _ : False (empty? q)
    _ rewrite eq = _

-- IsQueue bundles RawQueue with proofs of a Queues correctness,
-- such as enqueue adding 1 to the Queue's size
record IsQueue {Q : Set a → Set a} (rawQ : RawQueue Q) : Set (suc a) where

  open RawQueue rawQ

  field
    empty-toList   : toList (empty {A = A}) ≡ []
    fromList-empty : empty {A = A} ≈ fromList []
