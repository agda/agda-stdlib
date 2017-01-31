------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe functions on floats
------------------------------------------------------------------------

module Unsafe.Data.Float where

open import Data.Float public

open import Data.Bool.Base using (Bool ; true ; false)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Unsafe.Relation.Binary.PropositionalEquality.TrustMe

infix 4 _≟_

_≟_ : (x y : Float) → Dec (x ≡ y)
x ≟ y with primFloatEquality x y
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _
