------------------------------------------------------------------------
-- The Agda standard library
--
-- The lifting of a strict order to incorporate a new supremum
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- This module is designed to be used with
-- Relation.Nullary.Construct.Add.Supremum

open import Relation.Binary

module Relation.Binary.Construct.Add.Supremum.Strict
  {a r} {A : Set a} (_<_ : Rel A r) where

open import Level using (_⊔_)
open import Data.Product
open import Function
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
import Relation.Binary.PropositionalEquality as P
open import Relation.Nullary.Construct.Add.Supremum
import Relation.Binary.Construct.Add.Supremum.Equality as Equality
import Relation.Binary.Construct.Add.Supremum.NonStrict as NonStrict

------------------------------------------------------------------------
-- Definition

data _<⁺_ : Rel (A ⁺) (a ⊔ r) where
  [_]    : {k l : A} → k < l → [ k ] <⁺ [ l ]
  [_]<⊤⁺ : (k : A)           → [ k ] <⁺ ⊤⁺

------------------------------------------------------------------------
-- Relational properties

[<]-injective : ∀ {k l} → [ k ] <⁺ [ l ] → k < l
[<]-injective [ p ] = p

<⁺-asym : Asymmetric _<_ → Asymmetric _<⁺_
<⁺-asym <-asym [ p ]    [ q ] = <-asym p q
<⁺-asym <-asym [ k ]<⊤⁺ ()

<⁺-trans : Transitive _<_ → Transitive _<⁺_
<⁺-trans <-trans [ p ] [ q ]    = [ <-trans p q ]
<⁺-trans <-trans [ p ] [ k ]<⊤⁺ = [ _ ]<⊤⁺

<⁺-dec : Decidable _<_ → Decidable _<⁺_
<⁺-dec _<?_ [ k ] [ l ] = Dec.map′ [_] [<]-injective (k <? l)
<⁺-dec _<?_ [ k ] ⊤⁺    = yes [ k ]<⊤⁺
<⁺-dec _<?_ ⊤⁺    [ l ] = no (λ ())
<⁺-dec _<?_ ⊤⁺    ⊤⁺    = no (λ ())

<⁺-irrelevant : Irrelevant _<_ → Irrelevant _<⁺_
<⁺-irrelevant <-irr [ p ]    [ q ]    = P.cong _ (<-irr p q)
<⁺-irrelevant <-irr [ k ]<⊤⁺ [ k ]<⊤⁺ = P.refl

module _ {e} {_≈_ : Rel A e} where

  open Equality _≈_

  <⁺-cmp : Trichotomous _≈_ _<_ → Trichotomous _≈⁺_ _<⁺_
  <⁺-cmp <-cmp ⊤⁺    ⊤⁺    = tri≈ (λ ()) ⊤⁺≈⊤⁺ (λ ())
  <⁺-cmp <-cmp ⊤⁺    [ l ] = tri> (λ ()) (λ ()) [ l ]<⊤⁺
  <⁺-cmp <-cmp [ k ] ⊤⁺    = tri< [ k ]<⊤⁺ (λ ()) (λ ())
  <⁺-cmp <-cmp [ k ] [ l ] with <-cmp k l
  ... | tri< a ¬b ¬c = tri< [ a ] (¬b ∘ [≈]-injective) (¬c ∘ [<]-injective)
  ... | tri≈ ¬a b ¬c = tri≈ (¬a ∘ [<]-injective) [ b ] (¬c ∘ [<]-injective)
  ... | tri> ¬a ¬b c = tri> (¬a ∘ [<]-injective) (¬b ∘ [≈]-injective) [ c ]

  <⁺-irrefl : Irreflexive _≈_ _<_ → Irreflexive _≈⁺_ _<⁺_
  <⁺-irrefl <-irrefl [ p ] [ q ] = <-irrefl p q
  <⁺-irrefl <-irrefl ⊤⁺≈⊤⁺ ()

  <⁺-respˡ-≈⁺ : _<_ Respectsˡ _≈_ → _<⁺_ Respectsˡ _≈⁺_
  <⁺-respˡ-≈⁺ <-respˡ-≈ [ p ] [ q ]      = [ <-respˡ-≈ p q ]
  <⁺-respˡ-≈⁺ <-respˡ-≈ [ p ] ([ l ]<⊤⁺) = [ _ ]<⊤⁺
  <⁺-respˡ-≈⁺ <-respˡ-≈ ⊤⁺≈⊤⁺ q          = q

  <⁺-respʳ-≈⁺ : _<_ Respectsʳ _≈_ → _<⁺_ Respectsʳ _≈⁺_
  <⁺-respʳ-≈⁺ <-respʳ-≈ [ p ] [ q ] = [ <-respʳ-≈ p q ]
  <⁺-respʳ-≈⁺ <-respʳ-≈ ⊤⁺≈⊤⁺ q     = q

  <⁺-resp-≈⁺ : _<_ Respects₂ _≈_ → _<⁺_ Respects₂ _≈⁺_
  <⁺-resp-≈⁺ = map <⁺-respʳ-≈⁺ <⁺-respˡ-≈⁺

module _ {r} {_≤_ : Rel A r} where

  open NonStrict _≤_

  <⁺-transʳ : Trans _≤_ _<_ _<_ → Trans _≤⁺_ _<⁺_ _<⁺_
  <⁺-transʳ <-transʳ [ p ] [ q ]    = [ <-transʳ p q ]
  <⁺-transʳ <-transʳ [ p ] [ k ]<⊤⁺ = [ _ ]<⊤⁺

  <⁺-transˡ : Trans _<_ _≤_ _<_ → Trans _<⁺_ _≤⁺_ _<⁺_
  <⁺-transˡ <-transˡ [ p ]    [ q ]       = [ <-transˡ p q ]
  <⁺-transˡ <-transˡ [ p ]    ([ _ ] ≤⊤⁺) = [ _ ]<⊤⁺
  <⁺-transˡ <-transˡ [ k ]<⊤⁺ (⊤⁺ ≤⊤⁺)    = [ k ]<⊤⁺

------------------------------------------------------------------------
-- Structures

module _ {e} {_≈_ : Rel A e} where

  open Equality _≈_

  <⁺-isStrictPartialOrder : IsStrictPartialOrder _≈_ _<_ →
                            IsStrictPartialOrder _≈⁺_ _<⁺_
  <⁺-isStrictPartialOrder strict = record
    { isEquivalence = ≈⁺-isEquivalence isEquivalence
    ; irrefl        = <⁺-irrefl irrefl
    ; trans         = <⁺-trans trans
    ; <-resp-≈      = <⁺-resp-≈⁺ <-resp-≈
    } where open IsStrictPartialOrder strict

  <⁺-isDecStrictPartialOrder : IsDecStrictPartialOrder _≈_ _<_ →
                               IsDecStrictPartialOrder _≈⁺_ _<⁺_
  <⁺-isDecStrictPartialOrder dectot = record
    { isStrictPartialOrder = <⁺-isStrictPartialOrder isStrictPartialOrder
    ; _≟_                  = ≈⁺-dec _≟_
    ; _<?_                 = <⁺-dec _<?_
    } where open IsDecStrictPartialOrder dectot

  <⁺-isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_ →
                          IsStrictTotalOrder _≈⁺_ _<⁺_
  <⁺-isStrictTotalOrder strictot = record
    { isEquivalence = ≈⁺-isEquivalence isEquivalence
    ; trans         = <⁺-trans trans
    ; compare       = <⁺-cmp compare
    } where open IsStrictTotalOrder strictot
