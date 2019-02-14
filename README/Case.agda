------------------------------------------------------------------------
-- The Agda standard library
--
-- Examples showing how the case expressions can be used with anonymous
-- pattern-matching lambda abstractions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README.Case where

open import Data.Fin   hiding (pred)
open import Data.Maybe hiding (from-just)
open import Data.Nat   hiding (pred)
open import Function

------------------------------------------------------------------------
-- Different types of pattern-matching lambdas

-- absurd pattern

empty : ∀ {a} {A : Set a} → Fin 0 → A
empty i = case i of λ ()

-- {}-delimited and ;-separated list of clauses
-- Note that they do not need to be on different lines

pred : ℕ → ℕ
pred n = case n of λ
  { zero    → zero
  ; (suc n) → n
  }

-- where-introduced and indentation-identified block of list of clauses

from-just : ∀ {a} {A : Set a} (x : Maybe A) → From-just x
from-just x = case x return From-just of λ where
  (just x) → x
  nothing  → _

------------------------------------------------------------------------
-- We can define some recursive functions with case

plus : ℕ → ℕ → ℕ
plus m n = case m of λ
   { zero    → n
   ; (suc m) → suc (plus m n)
   }

div2 : ℕ → ℕ
div2 zero    = zero
div2 (suc m) = case m of λ where
  zero     → zero
  (suc m') → suc (div2 m')
