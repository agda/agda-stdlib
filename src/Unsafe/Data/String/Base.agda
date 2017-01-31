------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe functions on strings
------------------------------------------------------------------------

module Unsafe.Data.String.Base where

open import Data.String.Base public

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Unsafe.Relation.Binary.PropositionalEquality.TrustMe

toList∘fromList : ∀ s → toList (fromList s) ≡ s
toList∘fromList s = trustMe

fromList∘toList : ∀ s → fromList (toList s) ≡ s
fromList∘toList s = trustMe
