------------------------------------------------------------------------
-- The Agda standard library
--
-- Argument information used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.Argument.Information where

open import Data.Product
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Reflection.Argument.Relevance as Relevance using (Relevance)
open import Reflection.Argument.Visibility as Visibility using (Visibility)

------------------------------------------------------------------------
-- Re-exporting the builtins publically

open import Agda.Builtin.Reflection public using (ArgInfo)
open ArgInfo public

------------------------------------------------------------------------
-- Operations

visibility : ArgInfo → Visibility
visibility (arg-info v _) = v

relevance : ArgInfo → Relevance
relevance (arg-info _ r) = r

------------------------------------------------------------------------
-- Decidable equality

arg-info-injective₁ : ∀ {v r v′ r′} → arg-info v r ≡ arg-info v′ r′ → v ≡ v′
arg-info-injective₁ refl = refl

arg-info-injective₂ : ∀ {v r v′ r′} → arg-info v r ≡ arg-info v′ r′ → r ≡ r′
arg-info-injective₂ refl = refl

arg-info-injective : ∀ {v r v′ r′} → arg-info v r ≡ arg-info v′ r′ → v ≡ v′ × r ≡ r′
arg-info-injective = < arg-info-injective₁ , arg-info-injective₂ >

_≟_ : Decidable (_≡_ {A = ArgInfo})
arg-info v r ≟ arg-info v′ r′ =
  Dec.map′ (uncurry (cong₂ arg-info))
           arg-info-injective
           (v Visibility.≟ v′ ×-dec r Relevance.≟ r′)
