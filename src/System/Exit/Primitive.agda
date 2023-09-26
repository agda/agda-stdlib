------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive System.Exit simple bindings to Haskell functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module System.Exit.Primitive where

open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.IO using (IO)

data ExitCode : Set where
  ExitSuccess : ExitCode
  ExitFailure : Int → ExitCode

{-# FOREIGN GHC data AgdaExitCode = AgdaExitSuccess | AgdaExitFailure Integer #-}
{-# COMPILE GHC ExitCode = data AgdaExitCode (AgdaExitSuccess | AgdaExitFailure) #-}

{-# FOREIGN GHC import qualified System.Exit as SE #-}

{-# FOREIGN GHC
toExitCode :: AgdaExitCode -> SE.ExitCode
toExitCode AgdaExitSuccess = SE.ExitSuccess
toExitCode (AgdaExitFailure n) = SE.ExitFailure (fromIntegral n)

fromExitCode :: SE.ExitCode -> AgdaExitCode
fromExitCode SE.ExitSuccess = AgdaExitSuccess
fromExitCode (SE.ExitFailure n) = AgdaExitFailure (fromIntegral n)
#-}

postulate
  exitWith : ∀ {a} {A : Set a} → ExitCode → IO A

{-# COMPILE GHC exitWith = \ _ _ -> SE.exitWith . toExitCode #-}
