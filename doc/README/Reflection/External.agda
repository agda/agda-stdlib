------------------------------------------------------------------------
-- The Agda standard library
--
-- How to use reflection to call external functions.
--
-- IMPORTANT: In order for this file to type-check you will need to add
-- a line `/usr/bin/expr` to your `~/.agda/executables` file. See the
-- section on Reflection in the Agda user manual for more details.
------------------------------------------------------------------------

{-# OPTIONS --without-K --allow-exec #-}

module README.Reflection.External where

open import Data.List.Base using ([]; _∷_)
open import Data.String.Base using (String; _++_)
open import Relation.Binary.PropositionalEquality

-- All the commands needed to make an external system call are included
-- in `Reflection.External`.

open import Reflection.External
  using (CmdSpec; runCmd)

-- The most important one is `CmdSpec` ("command specification")
-- which allows ones to specify the external command being called, its
-- arguments and the contents of stdin.

-- Here we define a simple command spec that takes two numbers and
-- uses the Unix `expr` command to add the two together.

add : String → String → CmdSpec
add x y = record
  { name  = "expr"
  ; args  = x ∷ "+" ∷ y  ∷ []
  ; input = ""
  }

-- The command can then be run using the `runCmd` macro. If no error
-- occured then by default the macro returns the result of `stdout`.
-- Otherwise the macro will terminate with a type error.

test : runCmd (add "1" "2") ≡ "3\n"
test = refl

-- If you are running a command that you know might be ill-formed
-- and result in an error then can use `unsafeRunCmd` instead that
-- returns a `Result` object containing the exit code and the contents
-- of both `stdout` and `stderr`.

open import Reflection.External
  using (unsafeRunCmd; result; exitFailure)

error = "/usr/bin/expr: non-integer argument\n"

test2 : unsafeRunCmd (add "a" "b") ≡ result (exitFailure 2) "" error
test2 = refl

-- For a more advanced use-case where SMT solvers are invoked from
-- Agda, see Schmitty (https://github.com/wenkokke/schmitty)
