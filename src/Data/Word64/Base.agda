------------------------------------------------------------------------
-- The Agda standard library
--
-- Machine words: basic type and conversion functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Word64.Base where

open import Algebra.Core using (Op₂)
open import Data.Nat.Base as ℕ using (ℕ)
open import Function.Base using (_on_; _∘₂′_)
open import Level using (zero)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

------------------------------------------------------------------------
-- Re-export built-ins publicly

open import Agda.Builtin.Word public
  using (Word64)
  renaming
  ( primWord64ToNat   to toℕ
  ; primWord64FromNat to fromℕ
  )

liftOp₂ : Op₂ ℕ → Op₂ Word64
liftOp₂ op = fromℕ ∘₂′ op on toℕ

infix 4 _≈_
_≈_ : Rel Word64 zero
_≈_ = _≡_ on toℕ

infix 4 _<_
_<_ : Rel Word64 zero
_<_ = ℕ._<_ on toℕ

infix 4 _≤_
_≤_ : Rel Word64 zero
_≤_ = ℕ._≤_ on toℕ
