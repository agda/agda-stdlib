------------------------------------------------------------------------
-- The Agda standard library
--
-- Argument information used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.Argument.Information where

open import Data.Product
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Reflection.Argument.Modality as Modality using (Modality)
open import Reflection.Argument.Visibility as Visibility using (Visibility)

private
  variable
    v v′ : Visibility
    m m′ : Modality

------------------------------------------------------------------------
-- Re-exporting the builtins publicly

open import Agda.Builtin.Reflection public using (ArgInfo)
open ArgInfo public

------------------------------------------------------------------------
-- Operations

visibility : ArgInfo → Visibility
visibility (arg-info v _) = v

modality : ArgInfo → Modality
modality (arg-info _ m) = m

------------------------------------------------------------------------
-- Decidable equality

arg-info-injective₁ : arg-info v m ≡ arg-info v′ m′ → v ≡ v′
arg-info-injective₁ refl = refl

arg-info-injective₂ : arg-info v m ≡ arg-info v′ m′ → m ≡ m′
arg-info-injective₂ refl = refl

arg-info-injective : arg-info v m ≡ arg-info v′ m′ → v ≡ v′ × m ≡ m′
arg-info-injective = < arg-info-injective₁ , arg-info-injective₂ >

_≟_ : DecidableEquality ArgInfo
arg-info v m ≟ arg-info v′ m′ =
  Dec.map′
    (uncurry (cong₂ arg-info))
    arg-info-injective
    (v Visibility.≟ v′ ×-dec m Modality.≟ m′)
