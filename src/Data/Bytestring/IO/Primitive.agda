------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive Bytestrings: IO operations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module Data.Bytestring.IO.Primitive where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)
open import Data.Bytestring.Primitive using (Bytestring)
open import IO.Primitive.Core using (IO)

postulate
  readFile : String → IO Bytestring
  writeFile : String → Bytestring → IO ⊤

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import Data.ByteString #-}
{-# COMPILE GHC readFile = Data.ByteString.readFile . T.unpack #-}
{-# COMPILE GHC writeFile = Data.ByteString.writeFile . T.unpack #-}
