------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences on strict orders of freely adding an infimum to a Set
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Construction.Free.Infimum.StrictOrder
       {a r} {A : Set a} (_<_ : Rel A r) where

open import Level
open import Data.Product
open import Function
open import Function.Equivalence using (equivalence)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.Construction.Free.Infimum

data _<₋_ : Rel (A ₋) r where
  ⊥⁺<[_] : (l : A)           → ⊥⁺    <₋ [ l ]
  []<[]  : {k l : A} → k < l → [ k ] <₋ [ l ]

[]<[]⁻¹ : ∀ {k l} → [ k ] <₋ [ l ] → k < l
[]<[]⁻¹ ([]<[] p) = p

<₋-asym : Asymmetric _<_ → Asymmetric _<₋_
<₋-asym <-asym ⊥⁺<[ l ]  ()
<₋-asym <-asym ([]<[] p) ([]<[] q) = <-asym p q

<₋-trans : Transitive _<_ → Transitive _<₋_
<₋-trans <-trans ⊥⁺<[ l ] ([]<[] q)  = ⊥⁺<[ _ ]
<₋-trans <-trans ([]<[] p) ([]<[] q) = []<[] (<-trans p q)

<₋-dec : Decidable _<_ → Decidable _<₋_
<₋-dec <-dec ⊥⁺    ⊥⁺    = no (λ ())
<₋-dec <-dec ⊥⁺    [ l ] = yes ⊥⁺<[ l ]
<₋-dec <-dec [ k ] ⊥⁺    = no (λ ())
<₋-dec <-dec [ k ] [ l ] = Dec.map (equivalence []<[] []<[]⁻¹) (<-dec k l)

<₋-irrelevance : Irrelevant _<_ → Irrelevant _<₋_
<₋-irrelevance <-irrelevance ⊥⁺<[ l ]  ⊥⁺<[ .l ] = P.refl
<₋-irrelevance <-irrelevance ([]<[] p) ([]<[] q) = P.cong _ (<-irrelevance p q)

module _ {e} {_≈_ : Rel A e} where

  open import Relation.Binary.Construction.Free.Infimum.Pointwise _≈_

  <₋-tri : Trichotomous _≈_ _<_ → Trichotomous _≈₋_ _<₋_
  <₋-tri <-tri ⊥⁺    ⊥⁺    = tri≈ (λ ()) ⊥⁺≈⊥⁺ (λ ())
  <₋-tri <-tri ⊥⁺    [ l ] = tri< ⊥⁺<[ l ] (λ ()) (λ ())
  <₋-tri <-tri [ k ] ⊥⁺    = tri> (λ ()) (λ ()) ⊥⁺<[ k ]
  <₋-tri <-tri [ k ] [ l ] with <-tri k l
  <₋-tri <-tri [ k ] [ l ] | tri< a ¬b ¬c = tri< ([]<[] a) (¬b ∘ []≈[]⁻¹) (¬c ∘ []<[]⁻¹)
  <₋-tri <-tri [ k ] [ l ] | tri≈ ¬a b ¬c = tri≈ (¬a ∘ []<[]⁻¹) ([]≈[] b) (¬c ∘ []<[]⁻¹)
  <₋-tri <-tri [ k ] [ l ] | tri> ¬a ¬b c = tri> (¬a ∘ []<[]⁻¹) (¬b ∘ []≈[]⁻¹) ([]<[] c)

  <₋-irrefl : Irreflexive _≈_ _<_ → Irreflexive _≈₋_ _<₋_
  <₋-irrefl <-irrefl ⊥⁺≈⊥⁺     ()
  <₋-irrefl <-irrefl ([]≈[] p) ([]<[] q) = <-irrefl p q

  <₋-respˡ-≈₋ : _<_ Respectsˡ _≈_ → _<₋_ Respectsˡ _≈₋_
  <₋-respˡ-≈₋ <-respˡ-≈ ⊥⁺≈⊥⁺     q         = q
  <₋-respˡ-≈₋ <-respˡ-≈ ([]≈[] p) ([]<[] q) = []<[] (<-respˡ-≈ p q)

  <₋-respʳ-≈₋ : _<_ Respectsʳ _≈_ → _<₋_ Respectsʳ _≈₋_
  <₋-respʳ-≈₋ <-respʳ-≈ ⊥⁺≈⊥⁺     q         = q
  <₋-respʳ-≈₋ <-respʳ-≈ ([]≈[] p) ⊥⁺<[ l ]  = ⊥⁺<[ _ ]
  <₋-respʳ-≈₋ <-respʳ-≈ ([]≈[] p) ([]<[] q) = []<[] (<-respʳ-≈ p q)

  <₋-resp-≈₋ : _<_ Respects₂ _≈_ → _<₋_ Respects₂ _≈₋_
  <₋-resp-≈₋ = map <₋-respʳ-≈₋ <₋-respˡ-≈₋

  <₋-isStrictPartialOrder :
    IsStrictPartialOrder _≈_ _<_ → IsStrictPartialOrder _≈₋_ _<₋_
  <₋-isStrictPartialOrder strict = record
    { isEquivalence = ≈₋-isEquivalence isEquivalence
    ; irrefl        = λ {x} → <₋-irrefl irrefl {x}
    ; trans         = λ {x} → <₋-trans trans {x}
    ; <-resp-≈      = <₋-resp-≈₋ <-resp-≈
    } where open IsStrictPartialOrder strict

  <₋-isDecStrictPartialOrder :
    IsDecStrictPartialOrder _≈_ _<_ → IsDecStrictPartialOrder _≈₋_ _<₋_
  <₋-isDecStrictPartialOrder dectot = record
    { isStrictPartialOrder = <₋-isStrictPartialOrder isStrictPartialOrder
    ; _≟_                  = ≈₋-dec _≟_
    ; _<?_                 = <₋-dec _<?_
    } where open IsDecStrictPartialOrder dectot

  <₋-isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_ → IsStrictTotalOrder _≈₋_ _<₋_
  <₋-isStrictTotalOrder strictot = record
    { isEquivalence = ≈₋-isEquivalence isEquivalence
    ; trans         = λ {x} → <₋-trans trans {x}
    ; compare       = <₋-tri compare
    } where open IsStrictTotalOrder strictot


module _ {r} {_≤_ : Rel A r} where

  open import Relation.Binary.Construction.Free.Infimum.Order _≤_

  <₋-transʳ : Trans _≤_ _<_ _<_ → Trans _≤₋_ _<₋_ _<₋_
  <₋-transʳ <-transʳ (⊥⁺≤ .⊥⁺) (⊥⁺<[ l ]) = ⊥⁺<[ l ]
  <₋-transʳ <-transʳ (⊥⁺≤ l)   ([]<[] q)  = ⊥⁺<[ _ ]
  <₋-transʳ <-transʳ ([]≤[] p) ([]<[] q)  = []<[] (<-transʳ p q)

  <₋-transˡ : Trans _<_ _≤_ _<_ → Trans _<₋_ _≤₋_ _<₋_
  <₋-transˡ <-transˡ ⊥⁺<[ l ]  ([]≤[] q) = ⊥⁺<[ _ ]
  <₋-transˡ <-transˡ ([]<[] p) ([]≤[] q) = []<[] (<-transˡ p q)

