------------------------------------------------------------------------
-- The Agda standard library
--
-- Floats
------------------------------------------------------------------------

module Data.Float where

open import Data.String.Base using (String)

------------------------------------------------------------------------
-- Re-export built-ins publically

open import Agda.Builtin.Float public
  using
  ( Float
  ; primFloatEquality
  ; primShowFloat
  )

------------------------------------------------------------------------
-- Operations

show : Float → String
show = primShowFloat
