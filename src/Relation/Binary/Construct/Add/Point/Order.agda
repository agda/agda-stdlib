------------------------------------------------------------------------
-- The Agda standard library
--
-- A pointwise lifting of a relation to incorporate an additional point,
-- assumed to be 'below' everything else in `Pointed A`.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

-- This module is designed to be used with
-- Relation.Nullary.Construct.Add.Point

open import Relation.Binary.Core using (Rel; _⇒_)

module Relation.Binary.Construct.Add.Point.Order
  {a ℓ} {A : Set a} (_≲_ : Rel A ℓ) where

open import Data.Product.Base using (_,_)
open import Level using (Level; _⊔_)
open import Function.Base using (id; _∘_; _∘′_)
import Relation.Binary.Construct.Add.Point.Equality as Equality
open import Relation.Binary.Structures
  using (IsPreorder; IsPartialOrder)
open import Relation.Binary.Definitions
  using (Reflexive; Transitive; Antisymmetric; Directed; Decidable; Irrelevant)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Relation.Nullary.Decidable.Core as Dec
  using (yes; no)
open import Relation.Nullary.Construct.Add.Point as Point
  using (Pointed; ∙ ;[_])


private
  variable
    ℓ′ : Level
    x∙ : Pointed A
    x y : A

------------------------------------------------------------------------
-- Definition

infix 4 _≲∙_

data _≲∙_ : Rel (Pointed A) (a ⊔ ℓ) where
  ∙≲_ : ∀ x∙  → ∙     ≲∙ x∙
  [_] : x ≲ y → [ x ] ≲∙ [ y ]

pattern ∙≲∙ = ∙≲ ∙

------------------------------------------------------------------------
-- Relational properties

[≲]-injective : [ x ] ≲∙ [ y ] → x ≲ y
[≲]-injective [ x≲y ] = x≲y

≲∙-refl : Reflexive _≲_ → Reflexive _≲∙_
≲∙-refl ≲-refl {∙}     = ∙≲∙ 
≲∙-refl ≲-refl {[ x ]} = [ ≲-refl ]

≲∙-trans : Transitive _≲_ → Transitive _≲∙_
≲∙-trans ≲-trans (∙≲ _)  _       = ∙≲ _
≲∙-trans ≲-trans [ x≲y ] [ y≲z ] = [ ≲-trans x≲y y≲z ]

≲∙-directed : Directed _≲_ → Directed _≲∙_
≲∙-directed dir ∙     ∙     = ∙ , ∙≲∙ , ∙≲∙
≲∙-directed dir [ x ] ∙     = let z , x≲z , _ = dir x x in [ z ] , [ x≲z ] , (∙≲ _)
≲∙-directed dir ∙     [ y ] = let z , _ , y≲z = dir y y in [ z ] , (∙≲ _) , [ y≲z ]
≲∙-directed dir [ x ] [ y ] = let z , x≲z , y≲z = dir x y in [ z ] , [ x≲z ] , [ y≲z ]

≲∙-dec : Decidable _≲_ → Decidable _≲∙_
≲∙-dec _≟_ ∙     _     = yes (∙≲ _)
≲∙-dec _≟_ [ x ] ∙     = no λ()
≲∙-dec _≟_ [ x ] [ y ] = Dec.map′ [_] [≲]-injective (x ≟ y)

≲∙-irrelevant : Irrelevant _≲_ → Irrelevant _≲∙_
≲∙-irrelevant ≲-irr (∙≲ _) (∙≲ _) = ≡.refl
≲∙-irrelevant ≲-irr [ p ]  [ q ]  = ≡.cong _ (≲-irr p q)

------------------------------------------------------------------------
-- Relativised to a putative `Setoid`

module _ {_≈_ : Rel A ℓ′} where

  open Equality _≈_

  ≲∙-reflexive : (_≈_ ⇒ _≲_) → (_≈∙_ ⇒ _≲∙_)
  ≲∙-reflexive ≲-reflexive ∙≈∙     = ∙≲∙
  ≲∙-reflexive ≲-reflexive [ x≈y ] = [ ≲-reflexive x≈y ]

  ≲∙-antisym : Antisymmetric _≈_ _≲_ →  Antisymmetric _≈∙_ _≲∙_
  ≲∙-antisym ≲-antisym ∙≲∙     ∙≲∙     = ∙≈∙
  ≲∙-antisym ≲-antisym [ x≤y ] [ y≤x ] = [ ≲-antisym x≤y y≤x ]

------------------------------------------------------------------------
-- Structures

  ≲∙-isPreorder : IsPreorder _≈_ _≲_ → IsPreorder _≈∙_ _≲∙_
  ≲∙-isPreorder ≲-isPreorder = record
    { isEquivalence = Equality.≈∙-isEquivalence _ isEquivalence
    ; reflexive  = ≲∙-reflexive reflexive
    ; trans = ≲∙-trans trans
    } where open IsPreorder ≲-isPreorder


  ≲∙-isPartialOrder : IsPartialOrder _≈_ _≲_ → IsPartialOrder _≈∙_ _≲∙_
  ≲∙-isPartialOrder ≲-isPartialOrder = record
    { isPreorder = ≲∙-isPreorder isPreorder
    ; antisym = ≲∙-antisym antisym
    } where open IsPartialOrder ≲-isPartialOrder
