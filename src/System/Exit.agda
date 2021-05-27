------------------------------------------------------------------------
-- The Agda standard library
--
-- Exiting the program.
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module System.Exit where

open import Level using (Level)
open import Data.Nat.Base using (ℕ)
open import Data.String.Base using (String)
open import Function.Base using (_$_)
open import IO using (IO; lift; _>>_; putStrLn)

------------------------------------------------------------------------
-- Re-exporting the ExitCode data structure

open import System.Exit.Primitive as Prim
  using ( ExitCode
        ; ExitSuccess
        ; ExitFailure
        )
  public

------------------------------------------------------------------------
-- Various exiting function

private
  variable
    a : Level
    A : Set a

exitWith : ExitCode → IO A
exitWith c = lift (Prim.exitWith c)

exitFailure : IO A
exitFailure = exitWith (ExitFailure 1)

exitSuccess : IO A
exitSuccess = exitWith ExitSuccess

die : String → IO A
die str = do
  putStrLn str
  exitFailure
