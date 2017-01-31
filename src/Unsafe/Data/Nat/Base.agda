------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe functions on natural numbers, basic types and operations
------------------------------------------------------------------------

module Unsafe.Data.Nat.Base where

open import Data.Nat.Base public
import Unsafe.Relation.Binary.PropositionalEquality.TrustMe as TrustMe

erase : ∀ {m n} → m ≤″ n → m ≤″ n
erase (less-than-or-equal eq) = less-than-or-equal (TrustMe.erase eq)
