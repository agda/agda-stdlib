------------------------------------------------------------------------
-- The Agda standard library
--
-- Floats: basic types and operations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Float.Base where

open import Data.Bool.Base using (T)
import Data.Word64.Base as Word64
import Data.Maybe.Base as Maybe
open import Function.Base using (_on_; _∘_)
open import Agda.Builtin.Equality
open import Relation.Binary.Core using (Rel)

------------------------------------------------------------------------
-- Re-export built-ins publically

open import Agda.Builtin.Float public
  using (Float)
  renaming
  -- Relations
  ( primFloatInequality        to infix 4 _≤ᵇ_
  ; primFloatEquality          to infix 4 _≡ᵇ_
  ; primFloatLess              to infix 4 _<ᵇ_
  ; primFloatIsInfinite        to isInfinite
  ; primFloatIsNaN             to isNaN
  ; primFloatIsNegativeZero    to isNegativeZero
  ; primFloatIsSafeInteger     to isSafeInteger
  -- Conversions
  ; primFloatToWord64          to toWord64
  ; primNatToFloat             to fromℕ
  ; primIntToFloat             to fromℤ
  ; primFloatRound             to round
  ; primFloatFloor             to ⌊_⌋
  ; primFloatCeiling           to ⌈_⌉
  ; primFloatToRatio           to toRatio
  ; primRatioToFloat           to fromRatio
  ; primFloatDecode            to decode
  ; primFloatEncode            to encode
  ; primShowFloat              to show
  -- Operations
  ; primFloatPlus              to infixl 6 _+_
  ; primFloatMinus             to infixl 6 _-_
  ; primFloatTimes             to infixl 7 _*_
  ; primFloatDiv               to infixl 7 _÷_
  ; primFloatPow               to infixl 8 _**_
  ; primFloatNegate            to infixr 9 -_
  ; primFloatSqrt              to sqrt
  ; primFloatExp               to infixr 9 e^_
  ; primFloatLog               to log
  ; primFloatSin               to sin
  ; primFloatCos               to cos
  ; primFloatTan               to tan
  ; primFloatASin              to asin
  ; primFloatACos              to acos
  ; primFloatATan              to atan
  ; primFloatATan2             to atan2
  ; primFloatSinh              to sinh
  ; primFloatCosh              to cosh
  ; primFloatTanh              to tanh
  ; primFloatASinh             to asinh
  ; primFloatACosh             to acosh
  ; primFloatATanh             to atanh
  )

infix 4 _≈_

_≈_ : Rel Float _
_≈_ = _≡_ on Maybe.map Word64.toℕ ∘ toWord64


infix 4 _≤_
_≤_ : Rel Float _
x ≤ y = T (x ≤ᵇ y)


------------------------------------------------------------------------
-- DEPRECATIONS

toWord = toWord64
{-# WARNING_ON_USAGE toWord
"Warning: toWord was deprecated in v2.1.
Please use toWord64 instead."
#-}
