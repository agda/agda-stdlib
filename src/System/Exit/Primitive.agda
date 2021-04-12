------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive System.Exit simple bindings to Haskell functions
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module System.Exit.Primitive where

open import Data.Nat.Base using (ℕ)
open import IO.Primitive using (IO)

data ExitCode : Set where
  ExitSuccess : ExitCode
  ExitFailure : ℕ → ExitCode

{-# FOREIGN GHC data AgdaExitCode = AgdaExitSuccess | AgdaExitFailure Integer #-}
{-# COMPILE GHC ExitCode = data AgdaExitCode (AgdaExitSuccess | AgdaExitFailure) #-}

{-# FOREIGN GHC import qualified System.Exit as SE #-}

{-# FOREIGN GHC
toExitCode :: AgdaExitCode -> SE.ExitCode
toExitCode AgdaExitSuccess = SE.ExitSuccess
toExitCode (AgdaExitFailure n) = SE.ExitFailure (fromIntegral n)
#-}

postulate
  exitWith : ∀ {a} {A : Set a} → ExitCode → IO A

{-# COMPILE GHC exitWith = \ _ _ -> SE.exitWith . toExitCode #-}
