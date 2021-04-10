------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of reflexive closures
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Relation.Binary.Construct.Closure.Reflexive.Properties where

open import Data.Product as Prod
open import Data.Sum.Base as Sum
open import Function.Equivalence using (_⇔_; equivalence)
open import Function.Base using (id)
open import Level
open import Relation.Binary hiding (_⇔_)
open import Relation.Binary.Construct.Closure.Reflexive
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Unary using (Pred)

private
  variable
    a b ℓ p q : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Relational properties

module _ {P : Rel A p} {Q : Rel B q} where

  =[]⇒ : ∀ {f : A → B} → P =[ f ]⇒ Q → ReflClosure P =[ f ]⇒ ReflClosure Q
  =[]⇒ x [ x∼y ] = [ x x∼y ]
  =[]⇒ x refl    = refl

module _ {_~_ : Rel A ℓ} where

  private
    _~ᵒ_ = ReflClosure _~_

  fromSum : ∀ {x y} → x ≡ y ⊎ x ~ y → x ~ᵒ y
  fromSum (inj₁ refl) = refl
  fromSum (inj₂ y) = [ y ]

  toSum : ∀ {x y} → x ~ᵒ y → x ≡ y ⊎ x ~ y
  toSum [ x∼y ] = inj₂ x∼y
  toSum refl = inj₁ refl

  ⊎⇔Refl : ∀ {a b} → (a ≡ b ⊎ a ~ b) ⇔ a ~ᵒ b
  ⊎⇔Refl = equivalence fromSum toSum

  sym : Symmetric _~_ → Symmetric _~ᵒ_
  sym ~-sym [ x∼y ] = [ ~-sym x∼y ]
  sym ~-sym refl    = refl

  trans : Transitive _~_ → Transitive _~ᵒ_
  trans ~-trans [ x∼y ] [ x∼y₁ ] = [ ~-trans x∼y x∼y₁ ]
  trans ~-trans [ x∼y ] refl     = [ x∼y ]
  trans ~-trans refl    [ x∼y ]  = [ x∼y ]
  trans ~-trans refl    refl     = refl

  antisym : (_≈_ : Rel A p) → Reflexive _≈_ →
            Asymmetric _~_ → Antisymmetric _≈_ _~ᵒ_
  antisym _≈_ ref asym [ x∼y ] [ y∼x ] = contradiction x∼y (asym y∼x)
  antisym _≈_ ref asym [ x∼y ] refl    = ref
  antisym _≈_ ref asym refl    _       = ref

  total : Trichotomous _≡_ _~_ → Total _~ᵒ_
  total compare x y with compare x y
  ... | tri< a _    _ = inj₁ [ a ]
  ... | tri≈ _ refl _ = inj₁ refl
  ... | tri> _ _    c = inj₂ [ c ]

  dec : Decidable {A = A} _≡_ → Decidable _~_ → Decidable _~ᵒ_
  dec ≡-dec ~-dec a b = Dec.map ⊎⇔Refl (≡-dec a b ⊎-dec ~-dec a b)

  decidable : Trichotomous _≡_ _~_ → Decidable _~ᵒ_
  decidable ~-tri a b with ~-tri a b
  ... | tri< a~b  _  _ = yes [ a~b ]
  ... | tri≈ _  refl _ = yes refl
  ... | tri> ¬a ¬b   _ = no λ { refl → ¬b refl ; [ p ] → ¬a p }

  respˡ : ∀ {P : REL A B p} → P Respectsˡ _~_ → P Respectsˡ _~ᵒ_
  respˡ p-respˡ-~ [ x∼y ] = p-respˡ-~ x∼y
  respˡ _         refl    = id

  respʳ : ∀ {P : REL B A p} → P Respectsʳ _~_ → P Respectsʳ _~ᵒ_
  respʳ = respˡ

module _ {_~_ : Rel A ℓ} {P : Pred A p} where

  resp : P Respects _~_ → P Respects (ReflClosure _~_)
  resp p-resp-~ [ x∼y ] = p-resp-~ x∼y
  resp _        refl    = id

module _ {_~_ : Rel A ℓ} {P : Rel A p} where

  resp₂ : P Respects₂ _~_ → P Respects₂ (ReflClosure _~_)
  resp₂ = Prod.map respˡ respʳ

------------------------------------------------------------------------
-- Structures

module _ {_~_ : Rel A ℓ} where

  private
    _~ᵒ_ = ReflClosure _~_

  isPreorder : Transitive _~_ → IsPreorder _≡_ _~ᵒ_
  isPreorder ~-trans = record
    { isEquivalence = PropEq.isEquivalence
    ; reflexive     = λ { refl → refl }
    ; trans         = trans ~-trans
    }

  isPartialOrder : IsStrictPartialOrder _≡_ _~_ → IsPartialOrder _≡_ _~ᵒ_
  isPartialOrder O = record
    { isPreorder = isPreorder O.trans
    ; antisym    = antisym _≡_ refl O.asym
    } where module O = IsStrictPartialOrder O

  isDecPartialOrder : IsDecStrictPartialOrder _≡_ _~_ → IsDecPartialOrder _≡_ _~ᵒ_
  isDecPartialOrder O = record
    { isPartialOrder = isPartialOrder O.isStrictPartialOrder
    ; _≟_            = O._≟_
    ; _≤?_           = dec O._≟_ O._<?_
    } where module O = IsDecStrictPartialOrder O

  isTotalOrder : IsStrictTotalOrder _≡_ _~_ → IsTotalOrder _≡_ _~ᵒ_
  isTotalOrder O = record
    { isPartialOrder = isPartialOrder isStrictPartialOrder
    ; total          = total compare
    } where open IsStrictTotalOrder O

  isDecTotalOrder : IsStrictTotalOrder _≡_ _~_ → IsDecTotalOrder _≡_ _~ᵒ_
  isDecTotalOrder O = record
    { isTotalOrder = isTotalOrder O
    ; _≟_          = _≟_
    ; _≤?_         = dec _≟_ _<?_
    } where open IsStrictTotalOrder O
