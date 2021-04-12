------------------------------------------------------------------------
-- The Agda standard library
--
-- IO only involving infinite objects
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module IO.Infinite where

open import Codata.Musical.Costring
open import Agda.Builtin.String
open import Data.Unit.Polymorphic.Base
import Data.Unit.Base as Unit0
open import IO.Base
import IO.Primitive as Prim
import IO.Primitive.Infinite as Prim
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

getContents : IO Costring
getContents = lift Prim.getContents

private
  lift′ : Prim.IO Unit0.⊤ → IO {a} ⊤
  lift′ io = lift (io Prim.>>= λ _ → Prim.return _)

writeFile : String → Costring → IO {a} ⊤
writeFile f s = lift′ (Prim.writeFile f s)

appendFile : String → Costring → IO {a} ⊤
appendFile f s = lift′ (Prim.appendFile f s)

putStr : Costring → IO {a} ⊤
putStr s = lift′ (Prim.putStr s)

putStrLn : Costring → IO {a} ⊤
putStrLn s = lift′ (Prim.putStrLn s)
