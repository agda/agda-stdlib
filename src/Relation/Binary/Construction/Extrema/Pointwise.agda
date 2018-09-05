------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences on pointwise equality of freely adding extrema to a Set
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Construction.Extrema.Pointwise
       {a e} {A : Set a} (_≈_ : Rel A e) where

open import Function
open import Function.Equivalence using (equivalence)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
import Relation.Binary.PropositionalEquality as P

open import Relation.Binary.Construction.Extrema
import Relation.Binary.Construction.Infimum.Pointwise _≈_ as Inf
open import Relation.Binary.Construction.Supremum.Pointwise Inf._≈₋_ as Sup
  renaming (_≈⁺_ to _≈±_)
  using ()
  public

pattern ⊥⁺≈⊥⁺ = Sup.[ Inf.⊥⁺≈⊥⁺ ]
pattern [_] p = Sup.[ Inf.[ p ] ]
pattern ⊤⁺≈⊤⁺ = Sup.⊤⁺≈⊤⁺

[_]⁻¹ : ∀ {k l} → [ k ] ≈± [ l ] → k ≈ l
[_]⁻¹ = Inf.[_]⁻¹ ∘′ Sup.[_]⁻¹

≈±-refl : Reflexive _≈_ → Reflexive _≈±_
≈±-refl = Sup.≈⁺-refl ∘′ Inf.≈₋-refl

≈±-sym : Symmetric _≈_ → Symmetric _≈±_
≈±-sym = Sup.≈⁺-sym ∘′ Inf.≈₋-sym

≈±-trans : Transitive _≈_ → Transitive _≈±_
≈±-trans = Sup.≈⁺-trans ∘′ Inf.≈₋-trans

≈±-dec : Decidable _≈_ → Decidable _≈±_
≈±-dec = Sup.≈⁺-dec ∘′ Inf.≈₋-dec

≈±-irrelevance : Irrelevant _≈_ → Irrelevant _≈±_
≈±-irrelevance = Sup.≈⁺-irrelevance ∘′ Inf.≈₋-irrelevance

≈±-substitutive : ∀ {ℓ} → Substitutive _≈_ ℓ → Substitutive _≈±_ ℓ
≈±-substitutive = Sup.≈⁺-substitutive ∘′ Inf.≈₋-substitutive

≈±-isEquivalence : IsEquivalence _≈_ → IsEquivalence _≈±_
≈±-isEquivalence = Sup.≈⁺-isEquivalence ∘′ Inf.≈₋-isEquivalence

≈±-isDecEquivalence : IsDecEquivalence _≈_ → IsDecEquivalence _≈±_
≈±-isDecEquivalence = Sup.≈⁺-isDecEquivalence ∘′ Inf.≈₋-isDecEquivalence
