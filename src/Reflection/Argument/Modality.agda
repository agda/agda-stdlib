------------------------------------------------------------------------
-- The Agda standard library
--
-- Modalities used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.Argument.Modality where

open import Data.Product
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Reflection.Argument.Relevance as Relevance using (Relevance)
open import Reflection.Argument.Quantity as Quantity using (Quantity)

private
  variable
    r r′ : Relevance
    q q′ : Quantity

------------------------------------------------------------------------
-- Re-exporting the builtins publicly

open import Agda.Builtin.Reflection public using (Modality)
open Modality public

------------------------------------------------------------------------
-- Operations

relevance : Modality → Relevance
relevance (modality r _) = r

quantity : Modality → Quantity
quantity (modality _ q) = q

------------------------------------------------------------------------
-- Decidable equality

modality-injective₁ : modality r q ≡ modality r′ q′ → r ≡ r′
modality-injective₁ refl = refl

modality-injective₂ : modality r q ≡ modality r′ q′ → q ≡ q′
modality-injective₂ refl = refl

modality-injective : modality r q ≡ modality r′ q′ → r ≡ r′ × q ≡ q′
modality-injective = < modality-injective₁ , modality-injective₂ >

_≟_ : DecidableEquality Modality
modality r q ≟ modality r′ q′ =
  Dec.map′
    (uncurry (cong₂ modality))
    modality-injective
    (r Relevance.≟ r′ ×-dec q Quantity.≟ q′)
