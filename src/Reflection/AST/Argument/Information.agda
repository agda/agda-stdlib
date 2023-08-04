------------------------------------------------------------------------
-- The Agda standard library
--
-- Argument information used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.AST.Argument.Information where

open import Data.Product.Base                          using (_×_; <_,_>; uncurry)
open import Relation.Nullary.Decidable                 using (map′; _×-dec_)
open import Relation.Binary                            using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong₂)

open import Reflection.AST.Argument.Modality as Modality using (Modality)
open import Reflection.AST.Argument.Visibility as Visibility using (Visibility)

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

infix 4 _≟_

_≟_ : DecidableEquality ArgInfo
arg-info v m ≟ arg-info v′ m′ =
  map′
    (uncurry (cong₂ arg-info))
    arg-info-injective
    (v Visibility.≟ v′ ×-dec m Modality.≟ m′)
