------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe functions on divisibility
------------------------------------------------------------------------

module Unsafe.Data.Nat.Divisibility where

open import Data.Nat.Divisibility public

open import Data.Nat
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Unsafe.Data.Nat.DivMod
open import Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- Divisibility is decidable.

infix 4 _∣?_

_∣?_ : Decidable _∣_
zero  ∣? zero                         = yes (0 ∣0)
zero  ∣? suc n                        = no ((λ ()) ∘′ 0∣⇒≡0)
suc m ∣? n                            with n divMod suc m
suc m ∣? .(q * suc m)                 | result q zero    refl =
  yes $ divides q refl
suc m ∣? .(1 + Fin.toℕ r + q * suc m) | result q (suc r) refl =
  no $ nonZeroDivisor-lemma m q (suc r) (λ())
