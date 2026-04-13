------------------------------------------------------------------------
-- The Agda standard library
--
-- The lifting of a strict order to incorporate new extrema
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- This module is designed to be used with
-- Relation.Nullary.Construct.Add.Extrema

open import Relation.Binary.Core using (Rel)

module Relation.Binary.Construct.Add.Extrema.Strict
  {a ℓ} {A : Set a} (_<_ : Rel A ℓ) where

open import Level
open import Function.Base using (_∘′_)
import Relation.Nullary.Construct.Add.Infimum as I using (⊥₋; [_])
open import Relation.Nullary.Construct.Add.Extrema using (⊥±; ⊤±; [_])
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
import Relation.Binary.Construct.Add.Infimum.Strict as AddInfimum
import Relation.Binary.Construct.Add.Supremum.Strict as AddSupremum
import Relation.Binary.Construct.Add.Extrema.Equality as Equality
import Relation.Binary.Construct.Add.Extrema.NonStrict as NonStrict
open import Relation.Binary.Definitions
  using (Asymmetric; Transitive; Decidable; Irrelevant; Trichotomous
        ; Irreflexive; Trans; _Respectsˡ_; _Respectsʳ_; _Respects₂_)
open import Relation.Binary.Structures
  using (IsStrictPartialOrder; IsDecStrictPartialOrder; IsStrictTotalOrder)

------------------------------------------------------------------------
-- Definition

private
  module Inf = AddInfimum _<_
  module Sup = AddSupremum Inf._<₋_

open Sup using () renaming (_<⁺_ to _<±_) public

------------------------------------------------------------------------
-- Useful pattern synonyms

pattern ⊥±<[_] l = Sup.[ Inf.⊥₋<[ l ] ]
pattern [_] p    = Sup.[ Inf.[ p ] ]
pattern ⊥±<⊤±    = Sup.[ I.⊥₋ ]<⊤⁺
pattern [_]<⊤± k = Sup.[ I.[ k ] ]<⊤⁺

------------------------------------------------------------------------
-- Relational properties

[<]-injective : ∀ {k l} → [ k ] <± [ l ] → k < l
[<]-injective = Inf.[<]-injective ∘′ Sup.[<]-injective

<±-asym : Asymmetric _<_ → Asymmetric _<±_
<±-asym = Sup.<⁺-asym ∘′ Inf.<₋-asym

<±-trans : Transitive _<_ → Transitive _<±_
<±-trans = Sup.<⁺-trans ∘′ Inf.<₋-trans

<±-dec : Decidable _<_ → Decidable _<±_
<±-dec = Sup.<⁺-dec ∘′ Inf.<₋-dec

<±-irrelevant : Irrelevant _<_ → Irrelevant _<±_
<±-irrelevant = Sup.<⁺-irrelevant ∘′ Inf.<₋-irrelevant

module _ {r} {_≤_ : Rel A r} where

  open NonStrict _≤_

  <±-transʳ : Trans _≤_ _<_ _<_ → Trans _≤±_ _<±_ _<±_
  <±-transʳ = Sup.<⁺-transʳ ∘′ Inf.<₋-transʳ

  <±-transˡ : Trans _<_ _≤_ _<_ → Trans _<±_ _≤±_ _<±_
  <±-transˡ = Sup.<⁺-transˡ ∘′ Inf.<₋-transˡ

------------------------------------------------------------------------
-- Relational properties + propositional equality

<±-cmp-≡ : Trichotomous _≡_ _<_ → Trichotomous _≡_ _<±_
<±-cmp-≡ = Sup.<⁺-cmp-≡ ∘′ Inf.<₋-cmp-≡

<±-irrefl-≡ : Irreflexive _≡_ _<_ → Irreflexive _≡_ _<±_
<±-irrefl-≡ = Sup.<⁺-irrefl-≡ ∘′ Inf.<₋-irrefl-≡

<±-respˡ-≡ : _<±_ Respectsˡ _≡_
<±-respˡ-≡ = Sup.<⁺-respˡ-≡

<±-respʳ-≡ : _<±_ Respectsʳ _≡_
<±-respʳ-≡ = Sup.<⁺-respʳ-≡

<±-resp-≡ : _<±_ Respects₂ _≡_
<±-resp-≡ = Sup.<⁺-resp-≡

------------------------------------------------------------------------
-- Relational properties + setoid equality

module _ {e} {_≈_ : Rel A e} where

  open Equality _≈_

  <±-cmp : Trichotomous _≈_ _<_ → Trichotomous _≈±_ _<±_
  <±-cmp = Sup.<⁺-cmp ∘′ Inf.<₋-cmp

  <±-irrefl : Irreflexive _≈_ _<_ → Irreflexive _≈±_ _<±_
  <±-irrefl = Sup.<⁺-irrefl ∘′ Inf.<₋-irrefl

  <±-respˡ-≈± : _<_ Respectsˡ _≈_ → _<±_ Respectsˡ _≈±_
  <±-respˡ-≈± = Sup.<⁺-respˡ-≈⁺ ∘′ Inf.<₋-respˡ-≈₋

  <±-respʳ-≈± : _<_ Respectsʳ _≈_ → _<±_ Respectsʳ _≈±_
  <±-respʳ-≈± = Sup.<⁺-respʳ-≈⁺ ∘′ Inf.<₋-respʳ-≈₋

  <±-resp-≈± : _<_ Respects₂ _≈_ → _<±_ Respects₂ _≈±_
  <±-resp-≈± = Sup.<⁺-resp-≈⁺ ∘′ Inf.<₋-resp-≈₋

------------------------------------------------------------------------
-- Structures + propositional equality

<±-isStrictPartialOrder-≡ : IsStrictPartialOrder _≡_ _<_ →
                            IsStrictPartialOrder _≡_ _<±_
<±-isStrictPartialOrder-≡ =
  Sup.<⁺-isStrictPartialOrder-≡ ∘′ Inf.<₋-isStrictPartialOrder-≡

<±-isDecStrictPartialOrder-≡ : IsDecStrictPartialOrder _≡_ _<_ →
                               IsDecStrictPartialOrder _≡_ _<±_
<±-isDecStrictPartialOrder-≡ =
  Sup.<⁺-isDecStrictPartialOrder-≡ ∘′ Inf.<₋-isDecStrictPartialOrder-≡

<±-isStrictTotalOrder-≡ : IsStrictTotalOrder _≡_ _<_ →
                          IsStrictTotalOrder _≡_ _<±_
<±-isStrictTotalOrder-≡ =
  Sup.<⁺-isStrictTotalOrder-≡ ∘′ Inf.<₋-isStrictTotalOrder-≡

------------------------------------------------------------------------
-- Structures + setoid equality

module _ {e} {_≈_ : Rel A e} where

  open Equality _≈_

  <±-isStrictPartialOrder : IsStrictPartialOrder _≈_ _<_ →
                            IsStrictPartialOrder _≈±_ _<±_
  <±-isStrictPartialOrder =
    Sup.<⁺-isStrictPartialOrder ∘′ Inf.<₋-isStrictPartialOrder

  <±-isDecStrictPartialOrder : IsDecStrictPartialOrder _≈_ _<_ →
                               IsDecStrictPartialOrder _≈±_ _<±_
  <±-isDecStrictPartialOrder =
    Sup.<⁺-isDecStrictPartialOrder ∘′ Inf.<₋-isDecStrictPartialOrder

  <±-isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_ →
                          IsStrictTotalOrder _≈±_ _<±_
  <±-isStrictTotalOrder =
    Sup.<⁺-isStrictTotalOrder ∘′ Inf.<₋-isStrictTotalOrder
