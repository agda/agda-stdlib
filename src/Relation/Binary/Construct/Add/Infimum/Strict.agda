------------------------------------------------------------------------
-- The Agda standard library
--
-- The lifting of a strict order to incorporate a new infimum
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

-- This module is designed to be used with
-- Relation.Nullary.Construct.Add.Infimum

open import Relation.Binary.Core using (Rel)

module Relation.Binary.Construct.Add.Infimum.Strict
  {a ℓ} {A : Set a} (_<_ : Rel A ℓ) where

open import Level using (_⊔_)
open import Data.Product.Base using (_,_; map)
open import Function.Base using (_∘_)
open import Induction.WellFounded using (WfRec; Acc; acc; WellFounded)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; subst)
import Relation.Binary.PropositionalEquality.Properties as ≡
  using (isEquivalence)
import Relation.Binary.Construct.Add.Infimum.Equality as Equality
  using (_≈₋_; ⊥₋≈⊥₋; ≈₋-isEquivalence; ≈₋-isDecEquivalence; ≈₋-refl; ≈₋-dec
        ; [_]; [≈]-injective)
import Relation.Binary.Construct.Add.Infimum.NonStrict as NonStrict
open import Relation.Binary.Structures
  using (IsStrictPartialOrder; IsDecStrictPartialOrder; IsStrictTotalOrder)
open import Relation.Binary.Definitions
  using (Asymmetric; Transitive; Decidable; Irrelevant; Irreflexive; Trans
        ; Trichotomous; tri≈; tri<; tri>; _Respectsˡ_; _Respectsʳ_; _Respects₂_)
open import Relation.Nullary.Construct.Add.Infimum
  using (⊥₋; [_]; _₋; ≡-dec; []-injective)
open import Relation.Nullary.Decidable.Core as Dec using (yes; no; map′)


------------------------------------------------------------------------
-- Definition

infix 4 _<₋_

data _<₋_ : Rel (A ₋) (a ⊔ ℓ) where
  ⊥₋<[_] : (l : A)           → ⊥₋    <₋ [ l ]
  [_]    : {k l : A} → k < l → [ k ] <₋ [ l ]

------------------------------------------------------------------------
-- Relational properties

[<]-injective : ∀ {k l} → [ k ] <₋ [ l ] → k < l
[<]-injective [ p ] = p

<₋-asym : Asymmetric _<_ → Asymmetric _<₋_
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
<₋-irrelevant <-irr ⊥₋<[ l ] ⊥₋<[ l ] = refl
<₋-irrelevant <-irr [ p ]    [ q ]    = cong _ (<-irr p q)

module _ {r} {_≤_ : Rel A r} where

  open NonStrict _≤_

  <₋-transʳ : Trans _≤_ _<_ _<_ → Trans _≤₋_ _<₋_ _<₋_
  <₋-transʳ <-transʳ (⊥₋≤ ⊥₋)  q   = q
  <₋-transʳ <-transʳ (⊥₋≤ _) [ q ] = ⊥₋<[ _ ]
  <₋-transʳ <-transʳ [ p ]   [ q ] = [ <-transʳ p q ]

  <₋-transˡ : Trans _<_ _≤_ _<_ → Trans _<₋_ _≤₋_ _<₋_
  <₋-transˡ <-transˡ ⊥₋<[ _ ] [ q ] = ⊥₋<[ _ ]
  <₋-transˡ <-transˡ [ p ]    [ q ] = [ <-transˡ p q ]

<₋-accessible-⊥₋ : Acc _<₋_ ⊥₋
<₋-accessible-⊥₋ = acc λ()

<₋-accessible[_] : ∀ {x} → Acc _<_ x → Acc _<₋_ [ x ]
<₋-accessible[_] = acc ∘ wf-acc
  where
  wf-acc : ∀ {x} → Acc _<_ x → WfRec _<₋_ (Acc _<₋_) [ x ]
  wf-acc _       ⊥₋<[ _ ] = <₋-accessible-⊥₋
  wf-acc (acc ih) [ y<x ] = <₋-accessible[ ih y<x ]

<₋-wellFounded : WellFounded _<_ → WellFounded _<₋_
<₋-wellFounded wf ⊥₋    = <₋-accessible-⊥₋
<₋-wellFounded wf [ x ] = <₋-accessible[ wf x ]

------------------------------------------------------------------------
-- Relational properties + propositional equality

<₋-cmp-≡ : Trichotomous _≡_ _<_ → Trichotomous _≡_ _<₋_
<₋-cmp-≡ <-cmp ⊥₋    ⊥₋    = tri≈ (λ ()) refl (λ ())
<₋-cmp-≡ <-cmp ⊥₋    [ l ] = tri< ⊥₋<[ l ] (λ ()) (λ ())
<₋-cmp-≡ <-cmp [ k ] ⊥₋    = tri> (λ ()) (λ ()) ⊥₋<[ k ]
<₋-cmp-≡ <-cmp [ k ] [ l ] with <-cmp k l
... | tri< a ¬b    ¬c = tri< [ a ] (¬b ∘ []-injective) (¬c ∘ [<]-injective)
... | tri≈ ¬a refl ¬c = tri≈ (¬a ∘ [<]-injective) refl (¬c ∘ [<]-injective)
... | tri> ¬a ¬b    c = tri> (¬a ∘ [<]-injective) (¬b ∘ []-injective) [ c ]

<₋-irrefl-≡ : Irreflexive _≡_ _<_ → Irreflexive _≡_ _<₋_
<₋-irrefl-≡ <-irrefl refl [ x ] = <-irrefl refl x

<₋-respˡ-≡ : _<₋_ Respectsˡ _≡_
<₋-respˡ-≡ = subst (_<₋ _)

<₋-respʳ-≡ : _<₋_ Respectsʳ _≡_
<₋-respʳ-≡ = subst (_ <₋_)

<₋-resp-≡ : _<₋_ Respects₂ _≡_
<₋-resp-≡ = <₋-respʳ-≡ , <₋-respˡ-≡

------------------------------------------------------------------------
-- Relational properties + setoid equality

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

------------------------------------------------------------------------
-- Structures + propositional equality

<₋-isStrictPartialOrder-≡ : IsStrictPartialOrder _≡_ _<_ →
                            IsStrictPartialOrder _≡_ _<₋_
<₋-isStrictPartialOrder-≡ strict = record
  { isEquivalence = ≡.isEquivalence
  ; irrefl        = <₋-irrefl-≡ irrefl
  ; trans         = <₋-trans trans
  ; <-resp-≈      = <₋-resp-≡
  } where open IsStrictPartialOrder strict

<₋-isDecStrictPartialOrder-≡ : IsDecStrictPartialOrder _≡_ _<_ →
                               IsDecStrictPartialOrder _≡_ _<₋_
<₋-isDecStrictPartialOrder-≡ dectot = record
  { isStrictPartialOrder = <₋-isStrictPartialOrder-≡ isStrictPartialOrder
  ; _≟_                  = ≡-dec _≟_
  ; _<?_                 = <₋-dec _<?_
  } where open IsDecStrictPartialOrder dectot

<₋-isStrictTotalOrder-≡ : IsStrictTotalOrder _≡_ _<_ →
                          IsStrictTotalOrder _≡_ _<₋_
<₋-isStrictTotalOrder-≡ strictot = record
  { isStrictPartialOrder = <₋-isStrictPartialOrder-≡ isStrictPartialOrder
  ; compare              = <₋-cmp-≡ compare
  } where open IsStrictTotalOrder strictot

------------------------------------------------------------------------
-- Structures + setoid equality

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
    { isStrictPartialOrder = <₋-isStrictPartialOrder isStrictPartialOrder
    ; compare              = <₋-cmp compare
    } where open IsStrictTotalOrder strictot
