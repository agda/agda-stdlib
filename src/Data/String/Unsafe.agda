------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe String operations and proofs
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}

module Data.String.Unsafe where

open import Data.String.Base

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)

------------------------------------------------------------------------
-- Properties of conversion functions

toList∘fromList : ∀ s → toList (fromList s) ≡ s
toList∘fromList s = trustMe

fromList∘toList : ∀ s → fromList (toList s) ≡ s
fromList∘toList s = trustMe
