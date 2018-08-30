------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe Float operations
------------------------------------------------------------------------

module Data.Float.Unsafe where

open import Data.Float
open import Data.Bool.Base using (false; true)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe

------------------------------------------------------------------------
-- Equality testing

infix 4 _≟_

_≟_ : (x y : Float) → Dec (x ≡ y)
x ≟ y with primFloatEquality x y
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _
