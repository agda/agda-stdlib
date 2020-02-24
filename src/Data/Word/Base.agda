------------------------------------------------------------------------
-- The Agda standard library
--
-- Machine words: basic type and conversion functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Word.Base where

open import Level using (zero)
import Data.Nat.Base as ℕ
open import Function
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Re-export built-ins publicly

open import Agda.Builtin.Word public
  using (Word64)
  renaming
  ( primWord64ToNat   to toℕ
  ; primWord64FromNat to fromℕ
  )

infix 4 _≈_
_≈_ : Rel Word64 zero
_≈_ = _≡_ on toℕ

infix 4 _<_
_<_ : Rel Word64 zero
_<_ = ℕ._<_ on toℕ
