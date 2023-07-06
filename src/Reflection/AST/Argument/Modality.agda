------------------------------------------------------------------------
-- The Agda standard library
--
-- Modalities used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.AST.Argument.Modality where

open import Data.Product.Base                          using (_×_; <_,_>; uncurry)
open import Relation.Nullary.Decidable                 using (map′; _×-dec_)
open import Relation.Binary                            using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong₂)

open import Reflection.AST.Argument.Relevance as Relevance using (Relevance)
open import Reflection.AST.Argument.Quantity as Quantity using (Quantity)

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

infix 4 _≟_

_≟_ : DecidableEquality Modality
modality r q ≟ modality r′ q′ =
  map′
    (uncurry (cong₂ modality))
    modality-injective
    (r Relevance.≟ r′ ×-dec q Quantity.≟ q′)
