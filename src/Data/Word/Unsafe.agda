------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe machine word operations
------------------------------------------------------------------------

module Data.Word.Unsafe where

import Data.Nat as ℕ
open import Data.Word using (Word64; toℕ)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.TrustMe

------------------------------------------------------------------------
-- An informative equality test.

_≟_ : (a b : Word64) → Dec (a ≡ b)
a ≟ b with toℕ a ℕ.≟ toℕ b
... | yes _ = yes trustMe
... | no  _ = no whatever
  where postulate whatever : _
