------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe functions on IO
------------------------------------------------------------------------

module Unsafe.IO where

import Unsafe.IO.Primitive as Prim
open import IO Prim.IO public

open import Coinduction
open import Data.Unit.Base
open import Data.String

{-# NON_TERMINATING #-}

run : ∀ {a} {A : Set a} → IO A → Prim.IO A
run (lift m)   = m
run (return x) = Prim.return x
run (m  >>= f) = Prim._>>=_ (run (♭ m )) λ x → run (♭ (f x))
run (m₁ >> m₂) = Prim._>>=_ (run (♭ m₁)) λ _ → run (♭ m₂)

------------------------------------------------------------------------
-- Simple lazy IO

-- Note that the functions below produce commands which, when
-- executed, may raise exceptions.

-- Note also that the semantics of these functions depends on the
-- version of the Haskell base library. If the version is 4.2.0.0 (or
-- later?), then the functions use the character encoding specified by
-- the locale. For older versions of the library (going back to at
-- least version 3) the functions use ISO-8859-1.

getContents : IO Costring
getContents = lift Prim.getContents

readFile : String → IO Costring
readFile f = lift (Prim.readFile f)

-- Reads a finite file. Raises an exception if the file path refers to
-- a non-physical file (like "/dev/zero").

readFiniteFile : String → IO String
readFiniteFile f = lift (Prim.readFiniteFile f)

writeFile∞ : String → Costring → IO ⊤
writeFile∞ f s =
  ♯ lift (Prim.writeFile f s) >>
  ♯ return _

writeFile : String → String → IO ⊤
writeFile f s = writeFile∞ f (toCostring s)

appendFile∞ : String → Costring → IO ⊤
appendFile∞ f s =
  ♯ lift (Prim.appendFile f s) >>
  ♯ return _

appendFile : String → String → IO ⊤
appendFile f s = appendFile∞ f (toCostring s)

putStr∞ : Costring → IO ⊤
putStr∞ s =
  ♯ lift (Prim.putStr s) >>
  ♯ return _

putStr : String → IO ⊤
putStr s = putStr∞ (toCostring s)

putStrLn∞ : Costring → IO ⊤
putStrLn∞ s =
  ♯ lift (Prim.putStrLn s) >>
  ♯ return _

putStrLn : String → IO ⊤
putStrLn s = putStrLn∞ (toCostring s)

