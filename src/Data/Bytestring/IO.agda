------------------------------------------------------------------------
-- The Agda standard library
--
-- Bytestrings: IO operations
------------------------------------------------------------------------

{-# OPTIONS --guardedness --cubical-compatible #-}

module Data.Bytestring.IO where

open import Agda.Builtin.String
open import IO using (IO; lift)
open import Data.Bytestring.Base using (Bytestring)
open import Data.Unit.Base using (⊤)

import Data.Bytestring.IO.Primitive as Prim

readFile : String → IO Bytestring
readFile fp = lift (Prim.readFile fp)

writeFile : String → Bytestring → IO ⊤
writeFile fp str = lift (Prim.writeFile fp str)
