------------------------------------------------------------------------
-- The Agda standard library
--
-- An example of how the Record module can be used
------------------------------------------------------------------------

-- Taken from Randy Pollack's paper "Dependently Typed Records in Type
-- Theory".

{-# OPTIONS --with-K #-}

module README.Data.Record where

open import Data.Product
open import Data.String
open import Function using (flip)
open import Level
open import Relation.Binary

import Data.Record as Record

-- Let us use strings as labels.

open Record String _≟_

-- Partial equivalence relations.

PER : Signature _
PER = ∅ , "S"     ∶ (λ _ → Set)
        , "R"     ∶ (λ r → r · "S" → r · "S" → Set)
        , "sym"   ∶ (λ r → Lift _ (Symmetric (r · "R")))
        , "trans" ∶ (λ r → Lift _ (Transitive (r · "R")))

-- Given a PER the converse relation is also a PER.

converse : (P : Record PER) →
           Record (PER With "S" ≔ (λ _ → P · "S")
                       With "R" ≔ (λ _ → flip (P · "R")))
converse P =
  rec (rec (_ ,
    lift λ {_} → lower (P · "sym")) ,
    lift λ {_} yRx zRy → lower (P · "trans") zRy yRx)
