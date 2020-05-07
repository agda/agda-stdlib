------------------------------------------------------------------------
-- The Agda standard library
--
-- Documentation for permutation over `List`s
------------------------------------------------------------------------

module README.Data.List.Relation.Binary.Permutation where

open import Algebra.Structures using (IsCommutativeMonoid)
open import Data.List.Base
open import Data.Nat using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; setoid)

------------------------------------------------------------------------
-- Permutations

-- As an alternative to pointwise equality you might consider two lists
-- to be equal if they contain the same elements regardless of the order
-- of the elements. This is known as either "set equality" or a
-- "permutation".

-- The easiest-to-use formalisation of this relation is found in the
-- module:

open import Data.List.Relation.Binary.Permutation.Propositional

-- The permutation relation is written as `_↭_` and has four
-- constructors. The first `refl` says that a list is always
-- a permutation of itself, the second `prep` says that if the
-- heads of the lists are the same they can be skipped, the third
-- `swap` says that the first two elements of the lists can be
-- swapped and the fourth `trans` says that permutation proofs
-- can be chained transitively.

-- For example a proof that two lists are a permutation of one
-- another can be written as follows:

lem₁ : 1 ∷ 2 ∷ 3 ∷ [] ↭ 3 ∷ 1 ∷ 2 ∷ []
lem₁ = trans (prep 1 (swap 2 3 refl)) (swap 1 3 refl)

-- In practice it is difficult to parse the constructors in the
-- proof above and hence understand why it holds. The
-- `PermutationReasoning` module can be used to write this proof
-- in a much more readable form:

open PermutationReasoning

lem₂ : 1 ∷ 2 ∷ 3 ∷ [] ↭ 3 ∷ 1 ∷ 2 ∷ []
lem₂ = begin
  1 ∷ 2 ∷ 3 ∷ []  ↭⟨ prep 1 (swap 2 3 refl) ⟩
  1 ∷ 3 ∷ 2 ∷ []  ↭⟨ swap 1 3 refl ⟩
  3 ∷ 1 ∷ 2 ∷ []  ∎

-- As might be expected, properties of the permutation relation may be
-- found in:

open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (map⁺; ++-isCommutativeMonoid)

lem₃ : ∀ (f : ℕ → ℕ) {xs ys : List ℕ} → xs ↭ ys → map f xs ↭ map f ys
lem₃ = map⁺

lem₄ : IsCommutativeMonoid {A = List ℕ} _↭_ _++_ []
lem₄ = ++-isCommutativeMonoid

-- Alternatively permutations using non-propositional equality can be
-- found in:

import Data.List.Relation.Binary.Permutation.Setoid
