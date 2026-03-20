------------------------------------------------------------------------
-- The Agda standard library
--
-- The lifting of a strict order to incorporate a new supremum
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- This module is designed to be used with
-- Relation.Nullary.Construct.Add.Supremum

open import Relation.Binary.Core using (Rel)

module Relation.Binary.Construct.Add.Supremum.Strict
  {a r} {A : Set a} (_<_ : Rel A r) where

open import Data.Product.Base using (_,_; map)
open import Function.Base using (_∘_)
open import Level using (_⊔_)
open import Relation.Binary.Definitions
  using (Asymmetric; Transitive; Decidable; Irrelevant; Irreflexive; Trans
        ; Trichotomous; tri≈; tri>; tri<; _Respectsˡ_; _Respectsʳ_; _Respects₂_)
open import Relation.Nullary.Construct.Add.Supremum
  using (⊤⁺; _⁺; [_]; ≡-dec; []-injective)
import Relation.Binary.Construct.Add.Supremum.Equality as Equality
  using (_≈⁺_; ⊤⁺≈⊤⁺; ≈⁺-isEquivalence; ≈⁺-dec; [≈]-injective; [_])
import Relation.Binary.Construct.Add.Supremum.NonStrict as NonStrict
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; subst)
import Relation.Binary.PropositionalEquality.Properties as ≡
open import Relation.Binary.Structures
  using (IsStrictPartialOrder; IsDecStrictPartialOrder; IsStrictTotalOrder)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Nullary.Decidable.Core using (yes; no)
import Relation.Nullary.Decidable as Dec using (map′)

------------------------------------------------------------------------
-- Definition

infix 4 _<⁺_

data _<⁺_ : Rel (A ⁺) (a ⊔ r) where
  [_]    : {k l : A} → k < l → [ k ] <⁺ [ l ]
  [_]<⊤⁺ : (k : A)           → [ k ] <⁺ ⊤⁺

------------------------------------------------------------------------
-- Relational properties

[<]-injective : ∀ {k l} → [ k ] <⁺ [ l ] → k < l
[<]-injective [ p ] = p

<⁺-asym : Asymmetric _<_ → Asymmetric _<⁺_
<⁺-asym <-asym [ p ]    [ q ] = <-asym p q

<⁺-trans : Transitive _<_ → Transitive _<⁺_
<⁺-trans <-trans [ p ] [ q ]    = [ <-trans p q ]
<⁺-trans <-trans [ p ] [ k ]<⊤⁺ = [ _ ]<⊤⁺

<⁺-dec : Decidable _<_ → Decidable _<⁺_
<⁺-dec _<?_ [ k ] [ l ] = Dec.map′ [_] [<]-injective (k <? l)
<⁺-dec _<?_ [ k ] ⊤⁺    = yes [ k ]<⊤⁺
<⁺-dec _<?_ ⊤⁺    [ l ] = no (λ ())
<⁺-dec _<?_ ⊤⁺    ⊤⁺    = no (λ ())

<⁺-irrelevant : Irrelevant _<_ → Irrelevant _<⁺_
<⁺-irrelevant <-irr [ p ]    [ q ]    = cong _ (<-irr p q)
<⁺-irrelevant <-irr [ k ]<⊤⁺ [ k ]<⊤⁺ = refl


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
-- Relational properties + propositional equality

<⁺-cmp-≡ : Trichotomous _≡_ _<_ → Trichotomous _≡_ _<⁺_
<⁺-cmp-≡ <-cmp ⊤⁺    ⊤⁺    = tri≈ (λ ()) refl (λ ())
<⁺-cmp-≡ <-cmp ⊤⁺    [ l ] = tri> (λ ()) (λ ()) [ l ]<⊤⁺
<⁺-cmp-≡ <-cmp [ k ] ⊤⁺    = tri< [ k ]<⊤⁺ (λ ()) (λ ())
<⁺-cmp-≡ <-cmp [ k ] [ l ] with <-cmp k l
... | tri< a ¬b    ¬c = tri< [ a ] (¬b ∘ []-injective) (¬c ∘ [<]-injective)
... | tri≈ ¬a refl ¬c = tri≈ (¬a ∘ [<]-injective) refl (¬c ∘ [<]-injective)
... | tri> ¬a ¬b    c = tri> (¬a ∘ [<]-injective) (¬b ∘ []-injective) [ c ]

<⁺-irrefl-≡ : Irreflexive _≡_ _<_ → Irreflexive _≡_ _<⁺_
<⁺-irrefl-≡ <-irrefl refl [ x ] = <-irrefl refl x

<⁺-respˡ-≡ : _<⁺_ Respectsˡ _≡_
<⁺-respˡ-≡ = subst (_<⁺ _)

<⁺-respʳ-≡ : _<⁺_ Respectsʳ _≡_
<⁺-respʳ-≡ = subst (_ <⁺_)

<⁺-resp-≡ : _<⁺_ Respects₂ _≡_
<⁺-resp-≡ = <⁺-respʳ-≡ , <⁺-respˡ-≡

------------------------------------------------------------------------
-- Relational properties + setoid equality

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

  <⁺-respˡ-≈⁺ : _<_ Respectsˡ _≈_ → _<⁺_ Respectsˡ _≈⁺_
  <⁺-respˡ-≈⁺ <-respˡ-≈ [ p ] [ q ]      = [ <-respˡ-≈ p q ]
  <⁺-respˡ-≈⁺ <-respˡ-≈ [ p ] ([ l ]<⊤⁺) = [ _ ]<⊤⁺
  <⁺-respˡ-≈⁺ <-respˡ-≈ ⊤⁺≈⊤⁺ q          = q

  <⁺-respʳ-≈⁺ : _<_ Respectsʳ _≈_ → _<⁺_ Respectsʳ _≈⁺_
  <⁺-respʳ-≈⁺ <-respʳ-≈ [ p ] [ q ] = [ <-respʳ-≈ p q ]
  <⁺-respʳ-≈⁺ <-respʳ-≈ ⊤⁺≈⊤⁺ q     = q

  <⁺-resp-≈⁺ : _<_ Respects₂ _≈_ → _<⁺_ Respects₂ _≈⁺_
  <⁺-resp-≈⁺ = map <⁺-respʳ-≈⁺ <⁺-respˡ-≈⁺

------------------------------------------------------------------------
-- Structures + propositional equality

<⁺-isStrictPartialOrder-≡ : IsStrictPartialOrder _≡_ _<_ →
                            IsStrictPartialOrder _≡_ _<⁺_
<⁺-isStrictPartialOrder-≡ strict = record
  { isEquivalence = ≡.isEquivalence
  ; irrefl        = <⁺-irrefl-≡ irrefl
  ; trans         = <⁺-trans trans
  ; <-resp-≈      = <⁺-resp-≡
  } where open IsStrictPartialOrder strict

<⁺-isDecStrictPartialOrder-≡ : IsDecStrictPartialOrder _≡_ _<_ →
                               IsDecStrictPartialOrder _≡_ _<⁺_
<⁺-isDecStrictPartialOrder-≡ dectot = record
  { isStrictPartialOrder = <⁺-isStrictPartialOrder-≡ isStrictPartialOrder
  ; _≟_                  = ≡-dec _≟_
  ; _<?_                 = <⁺-dec _<?_
  } where open IsDecStrictPartialOrder dectot

<⁺-isStrictTotalOrder-≡ : IsStrictTotalOrder _≡_ _<_ →
                          IsStrictTotalOrder _≡_ _<⁺_
<⁺-isStrictTotalOrder-≡ strictot = record
  { isStrictPartialOrder = <⁺-isStrictPartialOrder-≡ isStrictPartialOrder
  ; compare              = <⁺-cmp-≡ compare
  } where open IsStrictTotalOrder strictot

------------------------------------------------------------------------
-- Structures + setoid equality

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
    { isStrictPartialOrder = <⁺-isStrictPartialOrder isStrictPartialOrder
    ; compare              = <⁺-cmp compare
    } where open IsStrictTotalOrder strictot

