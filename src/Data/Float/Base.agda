------------------------------------------------------------------------
-- The Agda standard library
--
-- Floats: basic types and operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Float.Base where

open import Relation.Binary.Core using (Rel)
import Data.Word.Base as Word
open import Function.Base using (_on_)
open import Agda.Builtin.Equality

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
  ; primFloatToWord64          to toWord
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

_≈_ : Rel Float _
_≈_ = Word._≈_ on toWord
