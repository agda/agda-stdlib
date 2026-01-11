------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic auxiliary definitions for monoid-like structures
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (RawMonoid)

module Algebra.Definitions.RawMonoid {a ℓ} (M : RawMonoid a ℓ) where

open import Data.Bool.Base as Bool using (Bool; true; false; if_then_else_)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Vec.Functional as Vector using (Vector)

open RawMonoid M renaming ( _∙_ to _+_ ; ε to 0# )

------------------------------------------------------------------------
-- Re-export definitions over a magma
------------------------------------------------------------------------

open import Algebra.Definitions.RawMagma rawMagma public

------------------------------------------------------------------------
-- Multiplication by natural number: action of the (0,+)-rawMonoid
------------------------------------------------------------------------
-- Standard definition

-- A simple definition, easy to use and prove properties about.

infixr 8 _×_

_×_ : ℕ → Carrier → Carrier
0     × x = 0#
suc n × x = x + (n × x)

------------------------------------------------------------------------
-- Type-checking optimised definition

-- For use in code where high performance at type-checking time is
-- important, e.g. solvers and tactics. Firstly it avoids unnecessarily
-- multiplying by the unit if possible, speeding up type-checking and
-- makes for much more readable proofs:
--
--     Standard definition:  x * 2 = x + x + 0#
--     Optimised definition: x * 2 = x + x
--
-- Secondly, associates to the left which, counterintuitive as it may
-- seem, also speeds up typechecking.
--
--     Standard definition: x * 3 = x + (x + (x + 0#))
--     Our definition:      x * 3 = (x + x) + x

infixl 8 _×′_

_×′_ : ℕ → Carrier → Carrier
0     ×′ x = 0#
1     ×′ x = x
suc n ×′ x = n ×′ x + x

{-# INLINE _×′_ #-}

------------------------------------------------------------------------
-- Summation
------------------------------------------------------------------------

sum : ∀ {n} → Vector Carrier n → Carrier
sum = Vector.foldr _+_ 0#

------------------------------------------------------------------------
-- 'Conjunction' with a Boolean: action of the Boolean (true,∧)-rawMonoid
------------------------------------------------------------------------

infixr 8 _∧_

_∧_ : Bool → Carrier → Carrier
b ∧ x = if b then x else 0#

-- tail-recursive optimisation
infixl 8 _∧′_∙_

_∧′_∙_ : Bool → Carrier → Carrier → Carrier
b ∧′ x ∙ y = if b then x + y else y
