------------------------------------------------------------------------
-- The Agda standard library
--
-- IO only involving infinite objects
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module IO.Infinite where

open import Codata.Musical.Costring using (Costring)
open import Agda.Builtin.String using (String)
open import Data.Unit.Polymorphic.Base using (⊤)
import Data.Unit.Base as Unit0 using (⊤)
open import IO.Base as Base using (IO; lift; lift′)
import IO.Primitive.Core as Prim using (IO; _>>=_; _>>_)
import IO.Primitive.Infinite as Prim
  using (getContents; writeFile; appendFile; putStr; putStrLn)
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

getContents : IO Costring
getContents = lift Prim.getContents

writeFile : String → Costring → IO {a} ⊤
writeFile f s = lift′ (Prim.writeFile f s)

appendFile : String → Costring → IO {a} ⊤
appendFile f s = lift′ (Prim.appendFile f s)

putStr : Costring → IO {a} ⊤
putStr s = lift′ (Prim.putStr s)

putStrLn : Costring → IO {a} ⊤
putStrLn s = lift′ (Prim.putStrLn s)
