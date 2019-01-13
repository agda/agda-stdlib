------------------------------------------------------------------------
-- The Agda standard library
--
-- An example showing how the Debug.Trace module can be used
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README.Debug.Trace where

------------------------------------------------------------------------
-- Sometimes compiled code can contain bugs.

-- Whether caused by the compiler or present in the source code already, they
-- can be hard to track. A primitive debugging technique is to strategically
-- insert calls to tracing functions which will display their String argument.

open import Data.String.Base using (_++_)
open import Debug.Trace

-- We can for instance add tracing messages to make sure an invariant is
-- respected or check in which order evaluation takes place in the backend
-- (which can inform our decision to use, or not, strictness primitives).

-- In the following example, we define a division operation on natural numbers
-- using the original dividend as the termination measure. We:

-- 1. check in the base case that when the fuel runs out then the updated dividend
--    is already zero.

-- 2. wrap the calls to _∸_ and go in respective calls to trace to see when all
--    of these thunks are forced: are we building a big thunk in go's second
--    argument or evaluating it as we go?

open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Nat.Show using (show)

div : ℕ → ℕ → Maybe ℕ
div m zero = nothing
div m n    = just (go m m) where

  -- invariants: m ≤ fuel
  -- result : m / n
  go : (fuel : ℕ) (m : ℕ) → ℕ
  go zero       m = trace ("Invariant: " ++ show m ++ " should be zero.") zero
  go (suc fuel) m =
    let m' = trace ("Thunk for step " ++ show fuel ++ " forced") (m ∸ n) in
    trace ("Recursive call for step " ++ show fuel) suc (go fuel m')

-- To observe the behaviour of this code, we need to compile it and run it.
-- To run it, we need a main function. We define a very basic one: run div,
-- and display its result if the run was successful.

-- We add two call to traces to see when div is evaluated and when the returned
-- number is forced (by a call to show).

open import IO

main =
  let r = trace "Call to div" (div 4 2)
      j = λ n → trace "Forcing the result wrapped in just." (putStrLn (show n)) in
  run (maybe′ j (return _) r)

-- We get the following trace where we can see that checking that the
-- maybe-solution is just-headed does not force the natural number. Once forced,
-- we observe that we indeed build a big thunk on go's second argument (all the
-- recursive calls happen first and then we force the thunks one by one).

-- Call to div
-- Forcing the result wrapped in just.
-- Recursive call for step 3
-- Recursive call for step 2
-- Recursive call for step 1
-- Recursive call for step 0
-- Thunk for step 0 forced
-- Thunk for step 1 forced
-- Thunk for step 2 forced
-- Thunk for step 3 forced
-- Invariant: 0 should be zero.
-- 4

-- We also notice that the result is incorrect: 4/2 is 2 and not 4. We quickly
-- notice that (div m (suc n)) will perform m recursive calls no matter what.
-- And at each call it will put add 1. We can fix this bug by adding a new first
-- equation to go:

-- go fuel zero = zero

-- Running the example again we observe that because we now need to check
-- whether go's second argument is zero, the function is more strict: we see
-- that recursive calls and thunk forcings are interleaved.

-- Call to div
-- Forcing the result wrapped in just.
-- Recursive call for step 3
-- Thunk for step 3 forced
-- Recursive call for step 2
-- Thunk for step 2 forced
-- 2
