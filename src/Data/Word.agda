------------------------------------------------------------------------
-- The Agda standard library
--
-- Machine words
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Word where

import Data.Nat as ℕ
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

------------------------------------------------------------------------
-- Re-export built-ins publically

open import Agda.Builtin.Word public
  using (Word64)
  renaming
  ( primWord64ToNat   to toℕ
  ; primWord64FromNat to fromℕ
  )
open import Agda.Builtin.Word.Properties renaming (primWord64ToNatInjective to toℕ-injective)

_≟_ : (a b : Word64) → Dec (a ≡ b)
a ≟ b with toℕ a ℕ.≟ toℕ b
(a ≟ b) | yes p = yes (toℕ-injective a b p)
(a ≟ b) | no ¬p = no λ eq → ¬p (cong toℕ eq)
