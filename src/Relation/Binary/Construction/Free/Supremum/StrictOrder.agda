------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences on strict orders of freely adding an infimum to a Set
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Construction.Free.Supremum.StrictOrder
       {a r} {A : Set a} (_<_ : Rel A r) where

open import Level
open import Data.Product
open import Function
open import Function.Equivalence using (equivalence)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.Construction.Free.Supremum

data _<⁺_ : Rel (A ⁺) r where
  [_]  : {k l : A} → k < l → [ k ] <⁺ [ l ]
  [_]<⊤⁺ : (k : A)           → [ k ] <⁺ ⊤⁺

[_]⁻¹ : ∀ {k l} → [ k ] <⁺ [ l ] → k < l
[ [ p ] ]⁻¹ = p

<⁺-asym : Asymmetric _<_ → Asymmetric _<⁺_
<⁺-asym <-asym [ p ]    [ q ] = <-asym p q
<⁺-asym <-asym [ k ]<⊤⁺ ()

<⁺-trans : Transitive _<_ → Transitive _<⁺_
<⁺-trans <-trans [ p ] [ q ]    = [ <-trans p q ]
<⁺-trans <-trans [ p ] [ k ]<⊤⁺ = [ _ ]<⊤⁺

<⁺-dec : Decidable _<_ → Decidable _<⁺_
<⁺-dec <-dec [ k ] [ l ] = Dec.map (equivalence [_] [_]⁻¹) (<-dec k l)
<⁺-dec <-dec [ k ] ⊤⁺    = yes [ k ]<⊤⁺
<⁺-dec <-dec ⊤⁺    [ l ] = no (λ ())
<⁺-dec <-dec ⊤⁺    ⊤⁺    = no (λ ())

<⁺-irrelevance : Irrelevant _<_ → Irrelevant _<⁺_
<⁺-irrelevance <-irrelevance [ p ]    [ q ]     = P.cong _ (<-irrelevance p q)
<⁺-irrelevance <-irrelevance [ k ]<⊤⁺ [ .k ]<⊤⁺ = P.refl

module _ {e} {_≈_ : Rel A e} where

  open import Relation.Binary.Construction.Free.Supremum.Pointwise _≈_ as IP
    hiding ([_]⁻¹)

  <⁺-tri : Trichotomous _≈_ _<_ → Trichotomous _≈⁺_ _<⁺_
  <⁺-tri <-tri [ k ] [ l ] with <-tri k l
  ... | tri< a ¬b ¬c = tri< [ a ] (¬b ∘ IP.[_]⁻¹) (¬c ∘ [_]⁻¹)
  ... | tri≈ ¬a b ¬c = tri≈ (¬a ∘ [_]⁻¹) [ b ] (¬c ∘ [_]⁻¹)
  ... | tri> ¬a ¬b c = tri> (¬a ∘ [_]⁻¹) (¬b ∘ IP.[_]⁻¹) [ c ]
  <⁺-tri <-tri ⊤⁺    [ l ] = tri> (λ ()) (λ ()) [ l ]<⊤⁺
  <⁺-tri <-tri [ k ] ⊤⁺    = tri< [ k ]<⊤⁺ (λ ()) (λ ())
  <⁺-tri <-tri ⊤⁺    ⊤⁺    = tri≈ (λ ()) ⊤⁺≈⊤⁺ (λ ())

  <⁺-irrefl : Irreflexive _≈_ _<_ → Irreflexive _≈⁺_ _<⁺_
  <⁺-irrefl <-irrefl [ p ] [ q ] = <-irrefl p q
  <⁺-irrefl <-irrefl ⊤⁺≈⊤⁺ ()

  <⁺-respˡ-≈⁺ : _<_ Respectsˡ _≈_ → _<⁺_ Respectsˡ _≈⁺_
  <⁺-respˡ-≈⁺ <-respˡ-≈ [ p ] [ q ]      = [ <-respˡ-≈ p q ]
  <⁺-respˡ-≈⁺ <-respˡ-≈ [ p ] ([ l ]<⊤⁺) = [ _ ]<⊤⁺
  <⁺-respˡ-≈⁺ <-respˡ-≈ ⊤⁺≈⊤⁺     q          = q

  <⁺-respʳ-≈⁺ : _<_ Respectsʳ _≈_ → _<⁺_ Respectsʳ _≈⁺_
  <⁺-respʳ-≈⁺ <-respʳ-≈ [ p ] [ q ] = [ <-respʳ-≈ p q ]
  <⁺-respʳ-≈⁺ <-respʳ-≈ ⊤⁺≈⊤⁺ q     = q

  <⁺-resp-≈⁺ : _<_ Respects₂ _≈_ → _<⁺_ Respects₂ _≈⁺_
  <⁺-resp-≈⁺ = map <⁺-respʳ-≈⁺ <⁺-respˡ-≈⁺

  <⁺-isStrictPartialOrder :
    IsStrictPartialOrder _≈_ _<_ → IsStrictPartialOrder _≈⁺_ _<⁺_
  <⁺-isStrictPartialOrder strict = record
    { isEquivalence = ≈⁺-isEquivalence isEquivalence
    ; irrefl        = λ {x} → <⁺-irrefl irrefl {x}
    ; trans         = λ {x} → <⁺-trans trans {x}
    ; <-resp-≈      = <⁺-resp-≈⁺ <-resp-≈
    } where open IsStrictPartialOrder strict

  <⁺-isDecStrictPartialOrder :
    IsDecStrictPartialOrder _≈_ _<_ → IsDecStrictPartialOrder _≈⁺_ _<⁺_
  <⁺-isDecStrictPartialOrder dectot = record
    { isStrictPartialOrder = <⁺-isStrictPartialOrder isStrictPartialOrder
    ; _≟_                  = ≈⁺-dec _≟_
    ; _<?_                 = <⁺-dec _<?_
    } where open IsDecStrictPartialOrder dectot

  <⁺-isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_ → IsStrictTotalOrder _≈⁺_ _<⁺_
  <⁺-isStrictTotalOrder strictot = record
    { isEquivalence = ≈⁺-isEquivalence isEquivalence
    ; trans         = λ {x} → <⁺-trans trans {x}
    ; compare       = <⁺-tri compare
    } where open IsStrictTotalOrder strictot


module _ {r} {_≤_ : Rel A r} where

  open import Relation.Binary.Construction.Free.Supremum.Order _≤_

  <⁺-transʳ : Trans _≤_ _<_ _<_ → Trans _≤⁺_ _<⁺_ _<⁺_
  <⁺-transʳ <-transʳ [ p ] [ q ]    = [ <-transʳ p q ]
  <⁺-transʳ <-transʳ [ p ] [ k ]<⊤⁺ = [ _ ]<⊤⁺

  <⁺-transˡ : Trans _<_ _≤_ _<_ → Trans _<⁺_ _≤⁺_ _<⁺_
  <⁺-transˡ <-transˡ [ p ]    [ q ]       = [ <-transˡ p q ]
  <⁺-transˡ <-transˡ [ p ]    ([ _ ] ≤⊤⁺) = [ _ ]<⊤⁺
  <⁺-transˡ <-transˡ [ k ]<⊤⁺ (.⊤⁺ ≤⊤⁺)   = [ k ]<⊤⁺

