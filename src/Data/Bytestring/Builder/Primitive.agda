------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive Bytestrings: builder type and functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module Data.Bytestring.Builder.Primitive where

open import Agda.Builtin.Nat
open import Agda.Builtin.String

open import Data.Word8.Primitive
open import Data.Bytestring.Primitive using (Bytestring)

infixr 6 _<>_

postulate
  -- Builder and execution
  Builder : Set
  toBytestring : Builder → Bytestring

  -- Assembling a builder
  bytestring : Bytestring → Builder
  word8 : Word8 → Builder
  empty : Builder
  _<>_ : Builder → Builder → Builder

{-# FOREIGN GHC import qualified Data.ByteString.Builder as Builder #-}
{-# FOREIGN GHC import qualified Data.ByteString.Lazy as Lazy #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC Builder = type Builder.Builder #-}
{-# COMPILE GHC toBytestring = Lazy.toStrict . Builder.toLazyByteString #-}
{-# COMPILE GHC bytestring = Builder.byteString #-}
{-# COMPILE GHC word8 = Builder.word8 #-}
{-# COMPILE GHC empty = mempty #-}
{-# COMPILE GHC _<>_ = mappend #-}
