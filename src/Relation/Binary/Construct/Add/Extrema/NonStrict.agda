------------------------------------------------------------------------
-- The Agda standard library
--
-- The lifting of a non-strict order to incorporate new extrema
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- This module is designed to be used with
-- Relation.Nullary.Construct.Add.Extrema

open import Relation.Binary.Core using (Rel; _⇒_)

module Relation.Binary.Construct.Add.Extrema.NonStrict
  {a ℓ} {A : Set a} (_≤_ : Rel A ℓ) where

open import Function.Base
open import Relation.Binary.Structures
  using (IsPreorder; IsPartialOrder; IsDecPartialOrder; IsTotalOrder
        ; IsDecTotalOrder)
open import Relation.Binary.Definitions
  using (Decidable; Transitive; Minimum; Maximum; Total; Irrelevant
        ; Antisymmetric; _Respectsˡ_; _Respectsʳ_; _Respects₂_)
open import Relation.Nullary.Construct.Add.Extrema using (⊥±; ⊤±; [_])
import Relation.Nullary.Construct.Add.Infimum as I using (⊥₋; [_])
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
import Relation.Binary.Construct.Add.Infimum.NonStrict as AddInfimum
import Relation.Binary.Construct.Add.Supremum.NonStrict as AddSupremum
import Relation.Binary.Construct.Add.Extrema.Equality as Equality

------------------------------------------------------------------------
-- Definition

private
  module Inf = AddInfimum _≤_
  module Sup = AddSupremum Inf._≤₋_

open Sup using () renaming (_≤⁺_ to _≤±_) public

------------------------------------------------------------------------
-- Useful pattern synonyms

pattern ⊥±≤⊥±    = Sup.[ Inf.⊥₋≤ I.⊥₋ ]
pattern ⊥±≤[_] l = Sup.[ Inf.⊥₋≤ I.[ l ] ]
pattern [_] p    = Sup.[ Inf.[ p ] ]
pattern ⊥±≤⊤±    = ⊥±    Sup.≤⊤⁺
pattern [_]≤⊤± k = [ k ] Sup.≤⊤⁺
pattern ⊤±≤⊤±    = ⊤±    Sup.≤⊤⁺

⊥±≤_ : ∀ k → ⊥± ≤± k
⊥±≤ ⊥±    = ⊥±≤⊥±
⊥±≤ [ k ] = ⊥±≤[ k ]
⊥±≤ ⊤±    = ⊥±≤⊤±

_≤⊤± : ∀ k → k ≤± ⊤±
⊥±    ≤⊤± = ⊥±≤⊤±
[ k ] ≤⊤± = [ k ]≤⊤±
⊤±    ≤⊤± = ⊤±≤⊤±

------------------------------------------------------------------------
-- Relational properties

[≤]-injective : ∀ {k l} → [ k ] ≤± [ l ] → k ≤ l
[≤]-injective = Inf.[≤]-injective ∘′ Sup.[≤]-injective

≤±-trans : Transitive _≤_ → Transitive _≤±_
≤±-trans = Sup.≤⁺-trans ∘′ Inf.≤₋-trans

≤±-minimum : Minimum _≤±_ ⊥±
≤±-minimum = ⊥±≤_

≤±-maximum : Maximum _≤±_ ⊤±
≤±-maximum = _≤⊤±

≤±-dec : Decidable _≤_ → Decidable _≤±_
≤±-dec = Sup.≤⁺-dec ∘′ Inf.≤₋-dec

≤±-total : Total _≤_ → Total _≤±_
≤±-total = Sup.≤⁺-total ∘′ Inf.≤₋-total

≤±-irrelevant : Irrelevant _≤_ → Irrelevant _≤±_
≤±-irrelevant = Sup.≤⁺-irrelevant ∘′ Inf.≤₋-irrelevant

------------------------------------------------------------------------
-- Relational properties + propositional equality

≤±-reflexive-≡ : (_≡_ ⇒ _≤_) → (_≡_ ⇒ _≤±_)
≤±-reflexive-≡ = Sup.≤⁺-reflexive-≡ ∘′ Inf.≤₋-reflexive-≡

≤±-antisym-≡ : Antisymmetric _≡_ _≤_ → Antisymmetric _≡_ _≤±_
≤±-antisym-≡ = Sup.≤⁺-antisym-≡ ∘′ Inf.≤₋-antisym-≡

≤±-respˡ-≡ : _≤±_ Respectsˡ _≡_
≤±-respˡ-≡ = Sup.≤⁺-respˡ-≡

≤±-respʳ-≡ : _≤±_ Respectsʳ _≡_
≤±-respʳ-≡ = Sup.≤⁺-respʳ-≡

≤±-resp-≡ : _≤±_ Respects₂ _≡_
≤±-resp-≡ = Sup.≤⁺-resp-≡

------------------------------------------------------------------------
-- Relational properties + setoid equality

module _ {e} {_≈_ : Rel A e} where

  open Equality _≈_

  ≤±-reflexive : (_≈_ ⇒ _≤_) → (_≈±_ ⇒ _≤±_)
  ≤±-reflexive = Sup.≤⁺-reflexive ∘′ Inf.≤₋-reflexive

  ≤±-antisym : Antisymmetric _≈_ _≤_ → Antisymmetric _≈±_ _≤±_
  ≤±-antisym = Sup.≤⁺-antisym ∘′ Inf.≤₋-antisym

  ≤±-respˡ-≈± : _≤_ Respectsˡ _≈_ → _≤±_ Respectsˡ _≈±_
  ≤±-respˡ-≈± = Sup.≤⁺-respˡ-≈⁺ ∘′ Inf.≤₋-respˡ-≈₋

  ≤±-respʳ-≈± : _≤_ Respectsʳ _≈_ → _≤±_ Respectsʳ _≈±_
  ≤±-respʳ-≈± = Sup.≤⁺-respʳ-≈⁺ ∘′ Inf.≤₋-respʳ-≈₋

  ≤±-resp-≈± : _≤_ Respects₂ _≈_ → _≤±_ Respects₂ _≈±_
  ≤±-resp-≈± = Sup.≤⁺-resp-≈⁺ ∘′ Inf.≤₋-resp-≈₋

------------------------------------------------------------------------
-- Structures + propositional equality

≤±-isPreorder-≡ : IsPreorder _≡_ _≤_ → IsPreorder _≡_ _≤±_
≤±-isPreorder-≡ = Sup.≤⁺-isPreorder-≡ ∘′ Inf.≤₋-isPreorder-≡

≤±-isPartialOrder-≡ : IsPartialOrder _≡_ _≤_ → IsPartialOrder _≡_ _≤±_
≤±-isPartialOrder-≡ = Sup.≤⁺-isPartialOrder-≡ ∘′ Inf.≤₋-isPartialOrder-≡

≤±-isDecPartialOrder-≡ : IsDecPartialOrder _≡_ _≤_ → IsDecPartialOrder _≡_ _≤±_
≤±-isDecPartialOrder-≡ = Sup.≤⁺-isDecPartialOrder-≡ ∘′ Inf.≤₋-isDecPartialOrder-≡

≤±-isTotalOrder-≡ : IsTotalOrder _≡_ _≤_ → IsTotalOrder _≡_ _≤±_
≤±-isTotalOrder-≡ = Sup.≤⁺-isTotalOrder-≡ ∘′ Inf.≤₋-isTotalOrder-≡

≤±-isDecTotalOrder-≡ : IsDecTotalOrder _≡_ _≤_ → IsDecTotalOrder _≡_ _≤±_
≤±-isDecTotalOrder-≡ = Sup.≤⁺-isDecTotalOrder-≡ ∘′ Inf.≤₋-isDecTotalOrder-≡

------------------------------------------------------------------------
-- Structures + setoid equality

module _ {e} {_≈_ : Rel A e} where

  open Equality _≈_

  ≤±-isPreorder : IsPreorder _≈_ _≤_ → IsPreorder _≈±_ _≤±_
  ≤±-isPreorder = Sup.≤⁺-isPreorder ∘′ Inf.≤₋-isPreorder

  ≤±-isPartialOrder : IsPartialOrder _≈_ _≤_ → IsPartialOrder _≈±_ _≤±_
  ≤±-isPartialOrder = Sup.≤⁺-isPartialOrder ∘′ Inf.≤₋-isPartialOrder

  ≤±-isDecPartialOrder : IsDecPartialOrder _≈_ _≤_ → IsDecPartialOrder _≈±_ _≤±_
  ≤±-isDecPartialOrder = Sup.≤⁺-isDecPartialOrder ∘′ Inf.≤₋-isDecPartialOrder

  ≤±-isTotalOrder : IsTotalOrder _≈_ _≤_ → IsTotalOrder _≈±_ _≤±_
  ≤±-isTotalOrder = Sup.≤⁺-isTotalOrder ∘′ Inf.≤₋-isTotalOrder

  ≤±-isDecTotalOrder : IsDecTotalOrder _≈_ _≤_ → IsDecTotalOrder _≈±_ _≤±_
  ≤±-isDecTotalOrder = Sup.≤⁺-isDecTotalOrder ∘′ Inf.≤₋-isDecTotalOrder
