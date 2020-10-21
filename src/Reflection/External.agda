------------------------------------------------------------------------
-- The Agda standard library
--
-- Support for system calls as part of reflection
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.External where

import Agda.Builtin.Reflection.External as Builtin

open import Data.Nat.Base using (ℕ; suc; zero; NonZero)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)
open import Data.String.Base as String using (String; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit.Base using (⊤; tt)
open import Function using (case_of_; _$_; _∘_)
open import Reflection hiding (name)

-- Type aliases for the various strings.

CmdName = String
StdIn   = String
StdErr  = String
StdOut  = String

-- Representation for exit codes, assuming 0 is consistently used to indicate
-- success across platforms.
data ExitCode : Set where
  exitSuccess : ExitCode
  exitFailure : (n : ℕ) {n≢0 : NonZero n} → ExitCode

-- Specification for a command.
record CmdSpec : Set where
  constructor cmdSpec
  field
    name  : CmdName     -- ^ Executable name (see ~/.agda/executables)
    args  : List String -- ^ Command-line arguments for executable
    input : StdIn       -- ^ Contents of standard input

-- Result of running a command.
record Result : Set where
  constructor result
  field
    exitCode : ExitCode -- ^ Exit code returned by the process
    output   : StdOut   -- ^ Contents of standard output
    error    : StdErr   -- ^ Contents of standard error

-- Convert a natural number to an exit code.
toExitCode : ℕ → ExitCode
toExitCode zero    = exitSuccess
toExitCode (suc n) = exitFailure (suc n)

-- Quote an exit code as an Agda term.
quoteExitCode : ExitCode → Term
quoteExitCode exitSuccess =
  con (quote exitSuccess) []
quoteExitCode (exitFailure n) =
  con (quote exitFailure) (vArg (lit (nat n)) ∷ hArg (con (quote tt) []) ∷ [])

-- Quote a result as an Agda term.
quoteResult : Result → Term
quoteResult (result exitCode output error) =
  con (quote result) $ vArg (quoteExitCode exitCode)
                     ∷ vArg (lit (string output))
                     ∷ vArg (lit (string error))
                     ∷ []

-- Run command from specification and return the full result.
--
-- NOTE: If the command fails, this macro still succeeds, and returns the
--       full result, including exit code and the contents of stderr.
--
unsafeRunCmdTC : CmdSpec → TC Result
unsafeRunCmdTC c = do
  (exitCode , (stdOut , stdErr))
    ← Builtin.execTC (CmdSpec.name c) (CmdSpec.args c) (CmdSpec.input c)
  return $ result (toExitCode exitCode) stdOut stdErr

macro
  unsafeRunCmd : CmdSpec → Term → TC ⊤
  unsafeRunCmd c hole = unsafeRunCmdTC c >>= unify hole ∘ quoteResult


-- Show a command for the user.
showCmdSpec : CmdSpec → String
showCmdSpec c = String.unwords $ CmdSpec.name c ∷ CmdSpec.args c


private
  -- Helper function for throwing an error from reflection.
  userError : ∀ {a} {A : Set a} → CmdSpec → StdOut × StdErr → TC A
  userError c (stdout , stderr) = typeError (strErr errMsg ∷ [])
    where
      errMsg : String
      errMsg = String.unlines
             $ ("Error while running command '" ++ showCmdSpec c ++ "'")
             ∷ ("Input:\n" ++ CmdSpec.input c)
             ∷ ("Output:\n" ++ stdout)
             ∷ ("Error:\n" ++ stderr)
             ∷ []


-- Run command from specification. If the command succeeds, it returns the
-- contents of stdout. Otherwise, it throws a type error with the contents
-- of stderr.
runCmdTC : CmdSpec → TC StdOut
runCmdTC c = do
  r ← unsafeRunCmdTC c
  let debugPrefix = ("user." ++ CmdSpec.name c)
  case Result.exitCode r of λ
    { exitSuccess → do
      debugPrint (debugPrefix ++ ".stderr") 10 (strErr (Result.error r) ∷ [])
      return $ Result.output r
    ; (exitFailure n) → do
      userError c (Result.output r , Result.error r)
    }

macro
  runCmd : CmdSpec → Term → TC ⊤
  runCmd c hole = runCmdTC c >>= unify hole ∘ lit ∘ string
