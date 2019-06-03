------------------------------------------------------------------------
-- The Agda standard library
--
-- Floats: basic types and operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Float.Base where

open import Relation.Binary.Core using (Rel)
import Data.Word.Base as Word
open import Function using (_on_)
open import Agda.Builtin.Equality

------------------------------------------------------------------------
-- Re-export built-ins publically

open import Agda.Builtin.Float public
  using (Float)
  renaming
  -- Relations
  ( primFloatEquality          to _≡ᵇ_
  ; primFloatLess              to _≤ᵇ_
  ; primFloatNumericalEquality to _≈ᵇ_
  ; primFloatNumericalLess     to _≲ᵇ_
  -- Conversions
  ; primShowFloat     to show
  ; primFloatToWord64 to toWord
  ; primNatToFloat    to fromℕ
  -- Operations
  ; primFloatPlus   to _+_
  ; primFloatMinus  to _-_
  ; primFloatTimes  to _*_
  ; primFloatNegate to -_
  ; primFloatDiv    to _÷_
  ; primFloatSqrt   to sqrt
  ; primRound       to round
  ; primFloor       to ⌊_⌋
  ; primCeiling     to ⌈_⌉
  ; primExp         to e^_
  ; primLog         to log
  ; primSin         to sin
  ; primCos         to cos
  ; primTan         to tan
  ; primASin        to asin
  ; primACos        to acos
  ; primATan        to atan
  )

_≈_ : Rel Float _
_≈_ = Word._≈_ on toWord

_<_ : Rel Float _
_<_ = Word._<_ on toWord
