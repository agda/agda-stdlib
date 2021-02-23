------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED, please use `Data.Record` directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Record {ℓ} (Label : Set ℓ) (_≟_ : Decidable {A = Label} _≡_) where

{-# WARNING_ON_IMPORT
"Record was deprecated in v1.1.
Use Data.Record instead."
#-}

open import Data.Record Label _≟_ public
