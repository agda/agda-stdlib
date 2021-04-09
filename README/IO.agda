------------------------------------------------------------------------
-- The Agda standard library
--
-- Simple examples of programs using IO
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

module README.IO where

open import Level
open import Data.Nat.Base
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_; lines)
open import Data.Unit.Polymorphic
open import IO

------------------------------------------------------------------------
-- Basic programs
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Hello World!

-- Minimal example of an IO program.
-- * The entrypoint of the executable is given type `Main`
-- * It is implemented using `run`, a function that converts a description
--   of an IO-computation into a computation that actually invokes the magic
--   primitives that will perform the side effects.

helloWorld : Main
helloWorld = run (putStrLn "Hello World!")

------------------------------------------------------------------------
-- Hello {{name}}!

-- We can of course write little auxiliary functions that may be used in
-- larger IO programs. Here we are going to first write a function displaying
-- "Hello {{name}}!" when {{name}} is passed as an argument.

-- `IO` primitives whose sole purpose is generating side effects (e.g.
-- printing a string on the screen) are typically given a level polymorphic
-- type which means we may need to add explicit level annotations.
-- Here we state that the `IO` computation will be at level zero (`0ℓ`).

sayHello : String → IO {0ℓ} ⊤
sayHello name = putStrLn ("Hello " ++ name ++ "!")

-- Functions can be sequenced using monadic combinators or `do` notations.
-- The two following definitions are equivalent. They start by asking the
-- user what their name is, listen for an answer and respond by saying hello
-- using the `sayHello` auxiliary function we just defined.

helloName : Main
helloName = run (putStrLn "What is your name?" >> getLine >>= sayHello)

doHelloName : Main
doHelloName = run do
  putStrLn "What is your name?"
  name ← getLine
  sayHello name

------------------------------------------------------------------------
-- (Co)Recursive programs
------------------------------------------------------------------------

------------------------------------------------------------------------
-- NO GUARDEDNESS

-- If you do not need to rely on guardedness for the function to be seen as
-- terminating (for instance because it is structural in an inductive argument)
-- then you can use `do` notations to write fairly readable programs.

-- Countdown to explosion
countdown : ℕ → IO {0ℓ} _
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
