------------------------------------------------------------------------
-- The Agda standard library
--
-- Documentation for pointwise lifting of relations over `List`s
------------------------------------------------------------------------

module README.Data.List.Relation.Binary.Pointwise where

open import Data.Nat using (ℕ; _<_; s≤s; z≤n)
open import Data.List using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; setoid)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Pointwise

-- One of the most basic ways to form a binary relation between two
-- lists of type `List A`, given a binary relation over `A`, is to say
-- that two lists are related if they are the same length and:
--   i) the first elements in the lists are related
--   ii) the second elements in the lists are related
--   iii) the third elements in the lists are related etc.
--   etc.
--
-- A formalisation of this "pointwise" lifting of a relation to lists
-- is found in:

open import Data.List.Relation.Binary.Pointwise

-- The same syntax to construct a list (`[]` & `_∷_`) is used to
-- construct proofs for the `Pointwise` relation. For example if you
-- want to prove that one list is strictly less than another list:

lem₁ : Pointwise _<_ (0 ∷ 2 ∷ 1 ∷ []) (1 ∷ 4 ∷ 2 ∷ [])
lem₁ = 0<1 ∷ 2<4 ∷ 1<2 ∷ []
  where
  0<1 = s≤s z≤n
  2<4 = s≤s (s≤s (s≤s z≤n))
  1<2 = s≤s 0<1

-- Lists that are related by `Pointwise` must be of the same length.
-- For example:

lem₂ : ¬ Pointwise _<_ (0 ∷ 2 ∷ []) (1 ∷ [])
lem₂ (0<1 ∷ ())

-- Proofs about pointwise, including that of the above fact are
-- also included in the module:

lem₃ : ∀ {xs ys} → Pointwise _<_ xs ys → length xs ≡ length ys
lem₃ = Pointwise-length
