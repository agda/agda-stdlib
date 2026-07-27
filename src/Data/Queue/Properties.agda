------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Queues, regardless of implementation
------------------------------------------------------------------------

module Data.Queue.Properties where

open import Data.Queue.QueueSpec using (RawQueue)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong)
open import Relation.Binary.Structures using (IsEquivalence)
open import Level using (Level; suc)

open RawQueue

private
  variable
    a b : Level
    A : Set a
    B : Set b

≈-refl : ∀ {Q : Set a → Set a} {RQ : RawQueue Q} {q : Q A} → (RQ ≈ q) q
≈-refl {_} {A} {Q} {RQ} {q} = {!q!}





