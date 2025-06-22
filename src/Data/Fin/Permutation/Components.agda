------------------------------------------------------------------------
-- The Agda standard library
--
-- Component functions of permutations found in `Data.Fin.Permutation`
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Permutation.Components where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using (Fin; suc; opposite; toℕ)
open import Data.Fin.Properties
  using (_≟_; ≟-diag; ≟-diag-refl
        ; opposite-prop; opposite-involutive; opposite-suc)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Nullary.Decidable.Core using (does; _because_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym)

------------------------------------------------------------------------
--  Functions
------------------------------------------------------------------------

-- 'transpose i j' swaps the places of 'i' and 'j'.

transpose : ∀ {n} → Fin n → Fin n → Fin n → Fin n
transpose i j k with does (k ≟ i)
... | true  = j
... | false with does (k ≟ j)
...   | true  = i
...   | false = k

------------------------------------------------------------------------
--  Properties
------------------------------------------------------------------------

transpose-iij : ∀ {n} (i j : Fin n) → transpose i i j ≡ j
transpose-iij i j with j ≟ i in j≟i
... | true  because [j≡i] = sym (invert [j≡i])
... | false because _ rewrite j≟i = refl

transpose-ijj : ∀ {n} (i j : Fin n) → transpose i j j ≡ i
transpose-ijj i j with j ≟ i
... | true  because [j≡i] = invert [j≡i]
... | false because _ rewrite ≟-diag-refl j = refl

transpose-iji : ∀ {n} (i j : Fin n) → transpose i j i ≡ j
transpose-iji i j rewrite ≟-diag-refl i = refl

transpose-transpose : ∀ {n} {i j k l : Fin n} →
                      transpose i j k ≡ l → transpose j i l ≡ k
transpose-transpose {n} {i} {j} {k} {l} eq with k ≟ i in k≟i
... | true  because [k≡i] rewrite ≟-diag (sym eq) = sym (invert [k≡i])
... | false because [k≢i] with k ≟ j in k≟j
...   | true  because [k≡j] rewrite eq | transpose-ijj j l = sym (invert [k≡j])
...   | false because [k≢j] rewrite eq | k≟j | k≟i = refl

transpose-inverse : ∀ {n} (i j : Fin n) {k} →
                    transpose i j (transpose j i k) ≡ k
transpose-inverse i j = transpose-transpose refl


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
