------------------------------------------------------------------------
-- The Agda standard library
--
-- Simple examples of programs using IO
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

module README.IO where

open import Data.Nat.Base
open import Data.Nat.Show using (show)
open import Data.String.Base using (String; lines)
open import Function.Base using (_$_)
open import IO
open import System.Environment

------------------------------------------------------------------------
-- NO GUARDEDNESS

-- If you do not need to rely on guardedness for the function to be seen as
-- terminating (for instance because it is structural in an inductive argument)
-- then you can use `do` notations to write fairly readable programs.

-- Countdown to explosion
countdown : ℕ → IO _
countdown zero      = putStrLn "BOOM!"
countdown m@(suc n) = do
  let str = show m
  putStrLn str
  countdown n

-- cat the content of a finite file
cat : String → IO _
cat fp = do
  content ← readFiniteFile fp
  let ls = lines content
  List.mapM′ putStrLn ls

open import Codata.Musical.Notation
open import Codata.Musical.Colist
open import Data.Bool
open import Data.Unit.Polymorphic.Base

------------------------------------------------------------------------
-- GUARDEDNESS

-- If you are performing coinduction on a potentially infinite piece of codata
-- then you need to rely on guardedness. That is to say that the coinductive
-- call needs to be obviously under a coinductive constructor and guarded by a
-- sharp (♯_).
-- In this case you cannot use the convenient combinators that make `do`-notations
-- and have to revert back to the underlying coinductive constructors.


-- Whether a colist is finite is semi decidable: just let the user wait until
-- you reach the end!
isFinite : ∀ {a} {A : Set a} → Colist A → IO Bool
isFinite []       = return true
isFinite (x ∷ xs) = seq (♯ return tt) (♯ isFinite (♭ xs))
