------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe natural number types and operations
------------------------------------------------------------------------

module Data.Nat.Unsafe where

open import Data.Nat.Base
import Relation.Binary.PropositionalEquality.TrustMe as TrustMe

erase : ∀ {m n} → m ≤″ n → m ≤″ n
erase (less-than-or-equal eq) = less-than-or-equal (TrustMe.erase eq)
