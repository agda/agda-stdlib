------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences on orders of freely adding extrema to a Set
------------------------------------------------------------------------
open import Relation.Binary

module Relation.Binary.Construction.Free.Extrema.Order
       {a r} {A : Set a} (_≤_ : Rel A r) where

open import Relation.Binary.Construction.Free.Extrema

open import Function

import Relation.Binary.Construction.Free.Infimum as Inf
import Relation.Binary.Construction.Free.Supremum as Sup
import Relation.Binary.Construction.Free.Infimum.Order _≤_ as Inf'
open import Relation.Binary.Construction.Free.Supremum.Order Inf'._≤₋_ as Sup'
  renaming (_≤⁺_ to _≤±_)
  using ()
  public

pattern ⊥⁺≤⊥⁺    = Sup'.[ Inf'.⊥⁺≤ Inf.⊥⁺ ]
pattern ⊥⁺≤[_] l = Sup'.[ Inf'.⊥⁺≤ Inf.[ l ] ]
pattern [_] p    = Sup'.[ Inf'.[ p ] ]
pattern ⊥⁺≤⊤⁺    = Sup.[ Inf.⊥⁺ ] Sup'.≤⊤⁺
pattern [_]≤⊤⁺ k = [ k ] Sup'.≤⊤⁺
pattern ⊤⁺≤⊤⁺    = Sup.⊤⁺ Sup'.≤⊤⁺

⊥⁺≤_ : ∀ k → ⊥⁺ ≤± k
⊥⁺≤ ⊥⁺    = ⊥⁺≤⊥⁺
⊥⁺≤ [ k ] = ⊥⁺≤[ k ]
⊥⁺≤ ⊤⁺    = ⊥⁺≤⊤⁺

_≤⊤⁺ : ∀ k → k ≤± ⊤⁺
⊥⁺    ≤⊤⁺ = ⊥⁺≤⊤⁺
[ k ] ≤⊤⁺ = [ k ]≤⊤⁺
⊤⁺    ≤⊤⁺ = ⊤⁺≤⊤⁺

[_]⁻¹ : ∀ {k l} → [ k ] ≤± [ l ] → k ≤ l
[_]⁻¹ = Inf'.[_]⁻¹ ∘′ Sup'.[_]⁻¹

module _ {e} {_≈_ : Rel A e} where

  open import Relation.Binary.Construction.Free.Extrema.Pointwise _≈_

  ≤±-reflexive : (_≈_ ⇒ _≤_) → (_≈±_ ⇒ _≤±_)
  ≤±-reflexive = Sup'.≤⁺-reflexive ∘′ Inf'.≤₋-reflexive

  ≤±-antisym : Antisymmetric _≈_ _≤_ → Antisymmetric _≈±_ _≤±_
  ≤±-antisym = Sup'.≤⁺-antisym ∘′ Inf'.≤₋-antisym

≤±-trans : Transitive _≤_ → Transitive _≤±_
≤±-trans = Sup'.≤⁺-trans ∘′ Inf'.≤₋-trans

≤±-minimum : Minimum _≤±_ ⊥⁺
≤±-minimum = ⊥⁺≤_

≤±-maximum : Maximum _≤±_ ⊤⁺
≤±-maximum = _≤⊤⁺

≤±-dec : Decidable _≤_ → Decidable _≤±_
≤±-dec = Sup'.≤⁺-dec ∘′ Inf'.≤₋-dec

≤±-total : Total _≤_ → Total _≤±_
≤±-total = Sup'.≤⁺-total ∘′ Inf'.≤₋-total

≤±-irrelevance : Irrelevant _≤_ → Irrelevant _≤±_
≤±-irrelevance = Sup'.≤⁺-irrelevance ∘′ Inf'.≤₋-irrelevance

module _ {e} {_≈_ : Rel A e} where

  open import Relation.Binary.Construction.Free.Extrema.Pointwise _≈_

  ≤±-isPreorder : IsPreorder _≈_ _≤_ → IsPreorder _≈±_ _≤±_
  ≤±-isPreorder = Sup'.≤⁺-isPreorder ∘′ Inf'.≤₋-isPreorder

  ≤±-isPartialOrder : IsPartialOrder _≈_ _≤_ → IsPartialOrder _≈±_ _≤±_
  ≤±-isPartialOrder = Sup'.≤⁺-isPartialOrder ∘′ Inf'.≤₋-isPartialOrder

  ≤±-isDecPartialOrder : IsDecPartialOrder _≈_ _≤_ → IsDecPartialOrder _≈±_ _≤±_
  ≤±-isDecPartialOrder = Sup'.≤⁺-isDecPartialOrder ∘′ Inf'.≤₋-isDecPartialOrder

  ≤±-isTotalOrder : IsTotalOrder _≈_ _≤_ → IsTotalOrder _≈±_ _≤±_
  ≤±-isTotalOrder = Sup'.≤⁺-isTotalOrder ∘′ Inf'.≤₋-isTotalOrder

  ≤±-isDecTotalOrder : IsDecTotalOrder _≈_ _≤_ → IsDecTotalOrder _≈±_ _≤±_
  ≤±-isDecTotalOrder = Sup'.≤⁺-isDecTotalOrder ∘′ Inf'.≤₋-isDecTotalOrder
