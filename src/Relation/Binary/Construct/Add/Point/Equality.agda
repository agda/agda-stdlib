------------------------------------------------------------------------
-- The Agda standard library
--
-- A pointwise lifting of a relation to incorporate an additional point.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- This module is designed to be used with
-- Relation.Nullary.Construct.Add.Point

open import Relation.Binary

module Relation.Binary.Construct.Add.Point.Equality
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

open import Function
import Relation.Binary.PropositionalEquality as P
open import Relation.Nullary
open import Relation.Nullary.Construct.Add.Point
import Relation.Nullary.Decidable as Dec

------------------------------------------------------------------------
-- Definition

data _≈∙_ : Rel (Pointed A) ℓ where
  ∙≈∙ :                     ∙     ≈∙ ∙
  [_] : {k l : A} → k ≈ l → [ k ] ≈∙ [ l ]

------------------------------------------------------------------------
-- Relational properties

[≈]-injective : ∀ {k l} → [ k ] ≈∙ [ l ] → k ≈ l
[≈]-injective [ k≈l ] = k≈l

≈∙-refl : Reflexive _≈_ → Reflexive _≈∙_
≈∙-refl ≈-refl {∙}     = ∙≈∙
≈∙-refl ≈-refl {[ k ]} = [ ≈-refl ]

≈∙-sym : Symmetric _≈_ → Symmetric _≈∙_
≈∙-sym ≈-sym ∙≈∙     = ∙≈∙
≈∙-sym ≈-sym [ x≈y ] = [ ≈-sym x≈y ]

≈∙-trans : Transitive _≈_ → Transitive _≈∙_
≈∙-trans ≈-trans ∙≈∙     ∙≈z     = ∙≈z
≈∙-trans ≈-trans [ x≈y ] [ y≈z ] = [ ≈-trans x≈y y≈z ]

≈∙-dec : Decidable _≈_ → Decidable _≈∙_
≈∙-dec _≟_ ∙     ∙     = yes ∙≈∙
≈∙-dec _≟_ ∙     [ l ] = no (λ ())
≈∙-dec _≟_ [ k ] ∙     = no (λ ())
≈∙-dec _≟_ [ k ] [ l ] = Dec.map′ [_] [≈]-injective (k ≟ l)

≈∙-irrelevant : Irrelevant _≈_ → Irrelevant _≈∙_
≈∙-irrelevant ≈-irr ∙≈∙   ∙≈∙   = P.refl
≈∙-irrelevant ≈-irr [ p ] [ q ] = P.cong _ (≈-irr p q)

≈∙-substitutive : ∀ {ℓ} → Substitutive _≈_ ℓ → Substitutive _≈∙_ ℓ
≈∙-substitutive ≈-subst P ∙≈∙   = id
≈∙-substitutive ≈-subst P [ p ] = ≈-subst (P ∘′ [_]) p

------------------------------------------------------------------------
-- Structures

≈∙-isEquivalence : IsEquivalence _≈_ → IsEquivalence _≈∙_
≈∙-isEquivalence ≈-isEquivalence = record
  { refl  = ≈∙-refl refl
  ; sym   = ≈∙-sym sym
  ; trans = ≈∙-trans trans
  } where open IsEquivalence ≈-isEquivalence

≈∙-isDecEquivalence : IsDecEquivalence _≈_ → IsDecEquivalence _≈∙_
≈∙-isDecEquivalence ≈-isDecEquivalence = record
  { isEquivalence = ≈∙-isEquivalence isEquivalence
  ; _≟_           = ≈∙-dec _≟_
  } where open IsDecEquivalence ≈-isDecEquivalence
