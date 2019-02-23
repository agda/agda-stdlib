------------------------------------------------------------------------
-- The Agda standard library
--
-- The lifting of a non-strict order to incorporate a new infimum
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- This module is designed to be used with
-- Relation.Nullary.Construct.Add.Infimum

open import Relation.Binary

module Relation.Binary.Construct.Add.Infimum.Strict
  {a ℓ} {A : Set a} (_<_ : Rel A ℓ) where

open import Level
open import Data.Product
open import Function
import Relation.Binary.PropositionalEquality as P
import Relation.Binary.Construct.Add.Infimum.Equality as Equality
import Relation.Binary.Construct.Add.Infimum.NonStrict as NonStrict
open import Relation.Nullary
open import Relation.Nullary.Construct.Add.Infimum
import Relation.Nullary.Decidable as Dec

------------------------------------------------------------------------
-- Definition

data _<₋_ : Rel (A ₋) ℓ where
  ⊥₋<[_] : (l : A)           → ⊥₋    <₋ [ l ]
  [_]    : {k l : A} → k < l → [ k ] <₋ [ l ]

------------------------------------------------------------------------
-- Relational properties

[<]-injective : ∀ {k l} → [ k ] <₋ [ l ] → k < l
[<]-injective [ p ] = p

<₋-asym : Asymmetric _<_ → Asymmetric _<₋_
<₋-asym <-asym ⊥₋<[ l ]  ()
<₋-asym <-asym [ p ] [ q ] = <-asym p q

<₋-trans : Transitive _<_ → Transitive _<₋_
<₋-trans <-trans ⊥₋<[ l ] [ q ] = ⊥₋<[ _ ]
<₋-trans <-trans [ p ]    [ q ] = [ <-trans p q ]

<₋-dec : Decidable _<_ → Decidable _<₋_
<₋-dec _<?_ ⊥₋    ⊥₋    = no (λ ())
<₋-dec _<?_ ⊥₋    [ l ] = yes ⊥₋<[ l ]
<₋-dec _<?_ [ k ] ⊥₋    = no (λ ())
<₋-dec _<?_ [ k ] [ l ] = Dec.map′ [_] [<]-injective (k <? l)

<₋-irrelevant : Irrelevant _<_ → Irrelevant _<₋_
<₋-irrelevant <-irr ⊥₋<[ l ] ⊥₋<[ l ] = P.refl
<₋-irrelevant <-irr [ p ]    [ q ]    = P.cong _ (<-irr p q)

module _ {e} {_≈_ : Rel A e} where

  open Equality _≈_

  <₋-cmp : Trichotomous _≈_ _<_ → Trichotomous _≈₋_ _<₋_
  <₋-cmp <-cmp ⊥₋    ⊥₋    = tri≈ (λ ()) ⊥₋≈⊥₋ (λ ())
  <₋-cmp <-cmp ⊥₋    [ l ] = tri< ⊥₋<[ l ] (λ ()) (λ ())
  <₋-cmp <-cmp [ k ] ⊥₋    = tri> (λ ()) (λ ()) ⊥₋<[ k ]
  <₋-cmp <-cmp [ k ] [ l ] with <-cmp k l
  ... | tri< a ¬b ¬c = tri< [ a ] (¬b ∘ [≈]-injective) (¬c ∘ [<]-injective)
  ... | tri≈ ¬a b ¬c = tri≈ (¬a ∘ [<]-injective) [ b ] (¬c ∘ [<]-injective)
  ... | tri> ¬a ¬b c = tri> (¬a ∘ [<]-injective) (¬b ∘ [≈]-injective) [ c ]

  <₋-irrefl : Irreflexive _≈_ _<_ → Irreflexive _≈₋_ _<₋_
  <₋-irrefl <-irrefl ⊥₋≈⊥₋ ()
  <₋-irrefl <-irrefl [ p ] [ q ] = <-irrefl p q

  <₋-respˡ-≈₋ : _<_ Respectsˡ _≈_ → _<₋_ Respectsˡ _≈₋_
  <₋-respˡ-≈₋ <-respˡ-≈ ⊥₋≈⊥₋ q     = q
  <₋-respˡ-≈₋ <-respˡ-≈ [ p ] [ q ] = [ <-respˡ-≈ p q ]

  <₋-respʳ-≈₋ : _<_ Respectsʳ _≈_ → _<₋_ Respectsʳ _≈₋_
  <₋-respʳ-≈₋ <-respʳ-≈ ⊥₋≈⊥₋ q        = q
  <₋-respʳ-≈₋ <-respʳ-≈ [ p ] ⊥₋<[ l ] = ⊥₋<[ _ ]
  <₋-respʳ-≈₋ <-respʳ-≈ [ p ] [ q ]    = [ <-respʳ-≈ p q ]

  <₋-resp-≈₋ : _<_ Respects₂ _≈_ → _<₋_ Respects₂ _≈₋_
  <₋-resp-≈₋ = map <₋-respʳ-≈₋ <₋-respˡ-≈₋

module _ {r} {_≤_ : Rel A r} where

  open NonStrict _≤_

  <₋-transʳ : Trans _≤_ _<_ _<_ → Trans _≤₋_ _<₋_ _<₋_
  <₋-transʳ <-transʳ (⊥₋≤ .⊥₋) (⊥₋<[ l ]) = ⊥₋<[ l ]
  <₋-transʳ <-transʳ (⊥₋≤ l)   [ q ]  = ⊥₋<[ _ ]
  <₋-transʳ <-transʳ [ p ]     [ q ]  = [ <-transʳ p q ]

  <₋-transˡ : Trans _<_ _≤_ _<_ → Trans _<₋_ _≤₋_ _<₋_
  <₋-transˡ <-transˡ ⊥₋<[ l ] [ q ] = ⊥₋<[ _ ]
  <₋-transˡ <-transˡ [ p ]    [ q ] = [ <-transˡ p q ]

------------------------------------------------------------------------
-- Structures

module _ {e} {_≈_ : Rel A e} where

  open Equality _≈_

  <₋-isStrictPartialOrder : IsStrictPartialOrder _≈_ _<_ →
                            IsStrictPartialOrder _≈₋_ _<₋_
  <₋-isStrictPartialOrder strict = record
    { isEquivalence = ≈₋-isEquivalence isEquivalence
    ; irrefl        = <₋-irrefl irrefl
    ; trans         = <₋-trans trans
    ; <-resp-≈      = <₋-resp-≈₋ <-resp-≈
    } where open IsStrictPartialOrder strict

  <₋-isDecStrictPartialOrder : IsDecStrictPartialOrder _≈_ _<_ →
                               IsDecStrictPartialOrder _≈₋_ _<₋_
  <₋-isDecStrictPartialOrder dectot = record
    { isStrictPartialOrder = <₋-isStrictPartialOrder isStrictPartialOrder
    ; _≟_                  = ≈₋-dec _≟_
    ; _<?_                 = <₋-dec _<?_
    } where open IsDecStrictPartialOrder dectot

  <₋-isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_ →
                          IsStrictTotalOrder _≈₋_ _<₋_
  <₋-isStrictTotalOrder strictot = record
    { isEquivalence = ≈₋-isEquivalence isEquivalence
    ; trans         = <₋-trans trans
    ; compare       = <₋-cmp compare
    } where open IsStrictTotalOrder strictot
