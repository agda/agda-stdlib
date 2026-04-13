------------------------------------------------------------------------
-- The Agda standard library
--
-- A pointwise lifting of a relation to incorporate new extrema.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- This module is designed to be used with
-- Relation.Nullary.Construct.Add.Extrema

open import Relation.Binary.Core using (Rel)

module Relation.Binary.Construct.Add.Extrema.Equality
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

open import Function.Base using (_∘′_)
open import Relation.Binary.Structures
  using (IsEquivalence; IsDecEquivalence)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive; Decidable; Irrelevant; Substitutive)
import Relation.Binary.Construct.Add.Infimum.Equality as AddInfimum
import Relation.Binary.Construct.Add.Supremum.Equality as AddSupremum
open import Relation.Nullary.Construct.Add.Extrema

------------------------------------------------------------------------
-- Definition

private
  module Inf = AddInfimum _≈_
  module Sup = AddSupremum (Inf._≈₋_)

open Sup using () renaming (_≈⁺_ to _≈±_) public

------------------------------------------------------------------------
-- Useful pattern synonyms

pattern ⊥±≈⊥± = Sup.[ Inf.⊥₋≈⊥₋ ]
pattern [_] p = Sup.[ Inf.[ p ] ]
pattern ⊤±≈⊤± = Sup.⊤⁺≈⊤⁺

------------------------------------------------------------------------
-- Relational properties

[≈]-injective : ∀ {k l} → [ k ] ≈± [ l ] → k ≈ l
[≈]-injective = Inf.[≈]-injective ∘′ Sup.[≈]-injective

≈±-refl : Reflexive _≈_ → Reflexive _≈±_
≈±-refl = Sup.≈⁺-refl ∘′ Inf.≈₋-refl

≈±-sym : Symmetric _≈_ → Symmetric _≈±_
≈±-sym = Sup.≈⁺-sym ∘′ Inf.≈₋-sym

≈±-trans : Transitive _≈_ → Transitive _≈±_
≈±-trans = Sup.≈⁺-trans ∘′ Inf.≈₋-trans

≈±-dec : Decidable _≈_ → Decidable _≈±_
≈±-dec = Sup.≈⁺-dec ∘′ Inf.≈₋-dec

≈±-irrelevant : Irrelevant _≈_ → Irrelevant _≈±_
≈±-irrelevant = Sup.≈⁺-irrelevant ∘′ Inf.≈₋-irrelevant

≈±-substitutive : ∀ {ℓ} → Substitutive _≈_ ℓ → Substitutive _≈±_ ℓ
≈±-substitutive = Sup.≈⁺-substitutive ∘′ Inf.≈₋-substitutive

------------------------------------------------------------------------
-- Structures

≈±-isEquivalence : IsEquivalence _≈_ → IsEquivalence _≈±_
≈±-isEquivalence = Sup.≈⁺-isEquivalence ∘′ Inf.≈₋-isEquivalence

≈±-isDecEquivalence : IsDecEquivalence _≈_ → IsDecEquivalence _≈±_
≈±-isDecEquivalence = Sup.≈⁺-isDecEquivalence ∘′ Inf.≈₋-isDecEquivalence
