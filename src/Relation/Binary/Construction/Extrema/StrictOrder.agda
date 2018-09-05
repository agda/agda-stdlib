------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences on strict orders of freely adding extrema to a Set
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Construction.Extrema.StrictOrder
       {a r} {A : Set a} (_<_ : Rel A r) where

open import Level
open import Function
open import Relation.Nullary

import Relation.Binary.Construction.Infimum as Inf
import Relation.Binary.Construction.Supremum as Sup
open import Relation.Binary.Construction.Extrema

import Relation.Binary.Construction.Infimum.StrictOrder _<_ as Inf'
open import Relation.Binary.Construction.Supremum.StrictOrder Inf'._<₋_ as Sup'
  renaming (_<⁺_ to _<±_)
  using ()
  public

pattern ⊥⁺<[_] l = Sup'.[ Inf'.⊥⁺<[ l ] ]
pattern [_] p    = Sup'.[ Inf'.[ p ] ]
pattern ⊥⁺<⊤⁺    = Sup'.[ Inf.⊥⁺ ]<⊤⁺
pattern [_]<⊤⁺ k = Sup'.[ Inf.[ k ] ]<⊤⁺

[_]⁻¹ : ∀ {k l} → [ k ] <± [ l ] → k < l
[_]⁻¹ = Inf'.[_]⁻¹ ∘′ Sup'.[_]⁻¹

<₋-asym : Asymmetric _<_ → Asymmetric _<±_
<₋-asym = Sup'.<⁺-asym ∘′ Inf'.<₋-asym

<±-trans : Transitive _<_ → Transitive _<±_
<±-trans = Sup'.<⁺-trans ∘′ Inf'.<₋-trans

<±-dec : Decidable _<_ → Decidable _<±_
<±-dec = Sup'.<⁺-dec ∘′ Inf'.<₋-dec

<±-irrelevance : Irrelevant _<_ → Irrelevant _<±_
<±-irrelevance = Sup'.<⁺-irrelevance ∘′ Inf'.<₋-irrelevance

module _ {e} {_≈_ : Rel A e} where

  open import Relation.Binary.Construction.Extrema.Pointwise _≈_ as IP
    hiding ([_]⁻¹)

  <±-tri : Trichotomous _≈_ _<_ → Trichotomous _≈±_ _<±_
  <±-tri = Sup'.<⁺-tri ∘′ Inf'.<₋-tri

  <±-irrefl : Irreflexive _≈_ _<_ → Irreflexive _≈±_ _<±_
  <±-irrefl = Sup'.<⁺-irrefl ∘′ Inf'.<₋-irrefl

  <±-respˡ-≈± : _<_ Respectsˡ _≈_ → _<±_ Respectsˡ _≈±_
  <±-respˡ-≈± = Sup'.<⁺-respˡ-≈⁺ ∘′ Inf'.<₋-respˡ-≈₋

  <±-respʳ-≈± : _<_ Respectsʳ _≈_ → _<±_ Respectsʳ _≈±_
  <±-respʳ-≈± = Sup'.<⁺-respʳ-≈⁺ ∘′ Inf'.<₋-respʳ-≈₋

  <±-resp-≈± : _<_ Respects₂ _≈_ → _<±_ Respects₂ _≈±_
  <±-resp-≈± = Sup'.<⁺-resp-≈⁺ ∘′ Inf'.<₋-resp-≈₋

  <±-isStrictPartialOrder :
    IsStrictPartialOrder _≈_ _<_ → IsStrictPartialOrder _≈±_ _<±_
  <±-isStrictPartialOrder =
    Sup'.<⁺-isStrictPartialOrder ∘′ Inf'.<₋-isStrictPartialOrder

  <±-isDecStrictPartialOrder :
    IsDecStrictPartialOrder _≈_ _<_ → IsDecStrictPartialOrder _≈±_ _<±_
  <±-isDecStrictPartialOrder =
    Sup'.<⁺-isDecStrictPartialOrder ∘′ Inf'.<₋-isDecStrictPartialOrder

  <±-isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_ → IsStrictTotalOrder _≈±_ _<±_
  <±-isStrictTotalOrder =
    Sup'.<⁺-isStrictTotalOrder ∘′ Inf'.<₋-isStrictTotalOrder

module _ {r} {_≤_ : Rel A r} where

  open import Relation.Binary.Construction.Extrema.Order _≤_

  <±-transʳ : Trans _≤_ _<_ _<_ → Trans _≤±_ _<±_ _<±_
  <±-transʳ = Sup'.<⁺-transʳ ∘′ Inf'.<₋-transʳ

  <±-transˡ : Trans _<_ _≤_ _<_ → Trans _<±_ _≤±_ _<±_
  <±-transˡ = Sup'.<⁺-transˡ ∘′ Inf'.<₋-transˡ
