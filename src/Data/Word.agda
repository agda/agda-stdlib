------------------------------------------------------------------------
-- The Agda standard library
--
-- Machine words
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Word where

------------------------------------------------------------------------
-- Re-export built-ins publically

open import Agda.Builtin.Word public
  using (Word64)
  renaming
  ( primWord64ToNat   to toℕ
  ; primWord64FromNat to fromℕ
  )
