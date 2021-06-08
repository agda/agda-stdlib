------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive System.Process simple bindings to Haskell functions
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

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

  system : String -> IO ExitCode

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

{-# COMPILE GHC callCommand cmd = callCommand (T.unpack cmd) #-}
{-# COMPILE GHC system cmd = map fromExitCode (system (T.unpack cmd)) #-}
{-# COMPILE GHC callProcess exe = callProcess (T.unpack exe) . map T.unpack #-}
{-# COMPILE GHC readProcess exe args = map T.pack . readProcess (T.unpack exe) (map T.unpack args) . T.unpack #-}
{-# COMPILE GHC readProcessWithExitCode exe args stdin =
           let (ex, out, err) = readProcessWithExitCode (T.unpack exe) (map T.unpack args) (T.unpack stdin) in
           (fromExitCode ex, T.pack out, T.pack err)
#-}
