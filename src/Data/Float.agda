------------------------------------------------------------------------
-- The Agda standard library
--
-- Floats
------------------------------------------------------------------------

module Data.Float where

open import Data.String.Base using (String)

open import Agda.Builtin.Float public
  using ( Float; primFloatEquality; primShowFloat )

show : Float → String
show = primShowFloat
