------------------------------------------------------------------------
-- The Agda standard library
--
-- IO only involving finite objects
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module IO.Finite where

open import Data.Unit.Polymorphic.Base
open import Agda.Builtin.String
import Data.Unit.Base as Unit0
open import IO.Base
import IO.Primitive as Prim
import IO.Primitive.Finite as Prim
open import Level

private
  variable
    a : Level

------------------------------------------------------------------------
-- Simple lazy IO

-- Note that the functions below produce commands which, when
-- executed, may raise exceptions.

-- Note also that the semantics of these functions depends on the
-- version of the Haskell base library. If the version is 4.2.0.0 (or
-- later?), then the functions use the character encoding specified by
-- the locale. For older versions of the library (going back to at
-- least version 3) the functions use ISO-8859-1.

getLine : IO String
getLine = lift Prim.getLine

-- Reads a finite file. Raises an exception if the file path refers to
-- a non-physical file (like "/dev/zero").

readFile : String → IO String
readFile f = lift (Prim.readFile f)

private
  lift′ : Prim.IO Unit0.⊤ → IO {a} ⊤
  lift′ io = lift (io Prim.>>= λ _ → Prim.return _)

writeFile : String → String → IO {a} ⊤
writeFile f s = lift′ (Prim.writeFile f s)

appendFile : String → String → IO {a} ⊤
appendFile f s = lift′ (Prim.appendFile f s)

putStr : String → IO {a} ⊤
putStr s = lift′ (Prim.putStr s)

putStrLn : String → IO {a} ⊤
putStrLn s = lift′ (Prim.putStrLn s)
