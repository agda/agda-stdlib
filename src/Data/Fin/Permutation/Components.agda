------------------------------------------------------------------------
-- The Agda standard library
--
-- Component functions of permutations found in `Data.Fin.Permutation`
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Permutation.Components where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base
open import Data.Fin.Properties
open import Data.Nat.Base as ℕ using (zero; suc; _∸_)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (proj₂)
open import Function.Base using (_∘_)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Nullary using (does; _because_; yes; no)
open import Relation.Nullary.Decidable using (dec-true; dec-false)
open import Relation.Binary.PropositionalEquality
open import Algebra.Definitions using (Involutive)
open ≡-Reasoning

--------------------------------------------------------------------------------
--  Functions
--------------------------------------------------------------------------------

-- 'tranpose i j' swaps the places of 'i' and 'j'.

transpose : ∀ {n} → Fin n → Fin n → Fin n → Fin n
transpose i j k with does (k ≟ i)
... | true  = j
... | false with does (k ≟ j)
...   | true  = i
...   | false = k

--------------------------------------------------------------------------------
--  Properties
--------------------------------------------------------------------------------

transpose-inverse : ∀ {n} (i j : Fin n) {k} →
                    transpose i j (transpose j i k) ≡ k
transpose-inverse i j {k} with k ≟ j
... | true  because [k≡j] rewrite dec-true (i ≟ i) refl = sym (invert [k≡j])
... | false because [k≢j] with k ≟ i
...   | true  because [k≡i]
        rewrite dec-false (j ≟ i) (invert [k≢j] ∘ trans (invert [k≡i]) ∘ sym)
                | dec-true (j ≟ j) refl
                = sym (invert [k≡i])
...   | false because [k≢i] rewrite dec-false (k ≟ i) (invert [k≢i])
                                  | dec-false (k ≟ j) (invert [k≢j]) = refl

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

reverse = opposite
{-# WARNING_ON_USAGE reverse
"Warning: reverse was deprecated in v2.0.
Please use opposite from Data.Fin.Base instead."
#-}

reverse-prop = opposite-prop
{-# WARNING_ON_USAGE reverse
"Warning: reverse-prop was deprecated in v2.0.
Please use opposite-prop from Data.Fin.Properties instead."
#-}

reverse-involutive = opposite-involutive
{-# WARNING_ON_USAGE reverse
"Warning: reverse-involutive was deprecated in v2.0.
Please use opposite-involutive from Data.Fin.Properties instead."
#-}

reverse-suc : ∀ {n} {i : Fin n} → toℕ (opposite (suc i)) ≡ toℕ (opposite i)
reverse-suc {i = i} = opposite-suc i
{-# WARNING_ON_USAGE reverse
"Warning: reverse-suc was deprecated in v2.0.
Please use opposite-suc from Data.Fin.Properties instead."
#-}
