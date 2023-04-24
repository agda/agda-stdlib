------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive System.Process simple bindings to Haskell functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module System.Process.Primitive where

open import Level using (Level)
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Foreign.Haskell using (Pair)
open import IO.Primitive using (IO)
open import System.Exit.Primitive using (ExitCode)

postulate

  callCommand : String → IO ⊤
  system      : String → IO ExitCode
  callProcess : String → List String → IO ⊤

  readProcess
    : String       -- Filename of the executable
    → List String  -- any arguments
    → String       -- standard input
    → IO String    -- stdout

  readProcessWithExitCode
    : String                                  -- Filename of the executable
    → List String                             -- any arguments
    → String                                  -- standard input
    → IO (Pair ExitCode (Pair String String)) -- exitcode, stdout, stderr

{-# FOREIGN GHC import System.Process  #-}
{-# FOREIGN GHC import qualified Data.Text as T  #-}
{-# FOREIGN GHC import MAlonzo.Code.System.Exit.Primitive #-}

{-# COMPILE GHC callCommand = \ cmd -> callCommand (T.unpack cmd) #-}
{-# COMPILE GHC system = \ cmd -> fmap fromExitCode (system (T.unpack cmd)) #-}
{-# COMPILE GHC callProcess = \ exe -> callProcess (T.unpack exe) . map T.unpack #-}
{-# COMPILE GHC readProcess = \ exe args -> fmap T.pack . readProcess (T.unpack exe) (map T.unpack args) . T.unpack #-}
{-# COMPILE GHC readProcessWithExitCode = \ exe args stdin ->
           do { (ex, out, err) <- readProcessWithExitCode (T.unpack exe) (map T.unpack args) (T.unpack stdin)
              ; pure (fromExitCode ex, (T.pack out, T.pack err))
              }
#-}
