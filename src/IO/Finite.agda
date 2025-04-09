------------------------------------------------------------------------
-- The Agda standard library
--
-- IO only involving finite objects
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module IO.Finite where

open import Data.Unit.Polymorphic.Base using (⊤)
open import Agda.Builtin.String using (String)
import Data.Unit.Base as Unit0 using (⊤)
open import IO.Base as Base using (IO; lift; lift′)
import IO.Primitive.Core as Prim using (IO; _>>=_; _>>_)
import IO.Primitive.Finite as Prim
  using (getLine; readFile; writeFile; appendFile; putStr; putStrLn)
open import Level using (Level; Lift; 0ℓ; suc)

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

writeFile : String → String → IO {a} ⊤
writeFile f s = lift′ (Prim.writeFile f s)

appendFile : String → String → IO {a} ⊤
appendFile f s = lift′ (Prim.appendFile f s)

putStr : String → IO {a} ⊤
putStr s = lift′ (Prim.putStr s)

putStrLn : String → IO {a} ⊤
putStrLn s = lift′ (Prim.putStrLn s)
