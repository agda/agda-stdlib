-----------------------------------------------------------------------
-- The Agda standard library
--
-- Calling external processes
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module System.Process where

open import Level using (Level)
open import Data.List.Base using (List)
open import Data.Product using (_×_; proj₁)
open import Data.String.Base using (String)
open import Data.Unit.Polymorphic using (⊤)
open import Foreign.Haskell.Coerce
open import IO.Base

open import System.Exit
import System.Process.Primitive as Prim

private
  variable
    ℓ : Level

callCommand : String → IO {ℓ} ⊤
callCommand cmd = lift′ (Prim.callCommand cmd)

system : String → IO ExitCode
system cmd = lift (Prim.system cmd)

callProcess : String → List String → IO {ℓ} ⊤
callProcess exe args = lift′ (Prim.callProcess exe args)

readProcess
    : String       -- Filename of the executable
    → List String  -- any arguments
    → String       -- standard input
    → IO String    -- stdout
readProcess exe args stdin = lift (Prim.readProcess exe args stdin)

readProcessWithExitCode
    : String                           -- Filename of the executable
    → List String                      -- any arguments
    → String                           -- standard input
    → IO (ExitCode × String × String)  -- exitcode, stdout, stderr
readProcessWithExitCode exe args stdin =
  lift (coerce Prim.readProcessWithExitCode exe args stdin)

callProcessWithExitCode : String → List String → IO ExitCode
callProcessWithExitCode exe args = proj₁ <$> readProcessWithExitCode exe args ""
