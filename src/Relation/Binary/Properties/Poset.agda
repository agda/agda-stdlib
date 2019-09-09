------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by posets
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Properties.Poset
   {p₁ p₂ p₃} (P : Poset p₁ p₂ p₃) where

open Poset P renaming (Carrier to A)

open import Function using (flip)
import Relation.Binary.Construct.NonStrictToStrict _≈_ _≤_ as ToStrict
import Relation.Binary.Properties.Preorder preorder as PreorderProperties
open import Relation.Nullary using (¬_)

private
  _≉_ : Rel A p₂
  x ≉ y = ¬ (x ≈ y)

------------------------------------------------------------------------
-- The _≥_ relation is also a poset.

infix 4 _≥_

_≥_ : Rel A p₃
x ≥ y = y ≤ x

open PreorderProperties public
  using ()
  renaming
  ( invIsPreorder to ≥-isPreorder
  ; invPreorder   to ≥-preorder
  )

≥-isPartialOrder : IsPartialOrder _≈_ _≥_
≥-isPartialOrder = record
  { isPreorder   = PreorderProperties.invIsPreorder
  ; antisym      = flip antisym
  }

≥-poset : Poset p₁ p₂ p₃
≥-poset = record
  { isPartialOrder = ≥-isPartialOrder
  }

open Poset ≥-poset public
  using ()
  renaming
  ( refl      to ≥-refl
  ; reflexive to ≥-reflexive
  ; trans     to ≥-trans
  ; antisym   to ≥-antisym
  )

------------------------------------------------------------------------
-- Partial orders can be turned into strict partial orders

infix 4 _<_

_<_ : Rel A _
_<_ = ToStrict._<_

<-isStrictPartialOrder : IsStrictPartialOrder _≈_ _<_
<-isStrictPartialOrder = ToStrict.<-isStrictPartialOrder isPartialOrder

<-strictPartialOrder : StrictPartialOrder _ _ _
<-strictPartialOrder = record
  { isStrictPartialOrder = <-isStrictPartialOrder
  }

open StrictPartialOrder <-strictPartialOrder public
  using ( <-resp-≈; <-respʳ-≈; <-respˡ-≈)
  renaming
  ( irrefl to <-irrefl
  ; asym   to <-asym
  ; trans  to <-trans
  )

<⇒≉ : ∀ {x y} → x < y → x ≉ y
<⇒≉ = ToStrict.<⇒≉

≤∧≉⇒< : ∀ {x y} → x ≤ y → x ≉ y → x < y
≤∧≉⇒< = ToStrict.≤∧≉⇒<

<⇒≱ : ∀ {x y} → x < y → ¬ (y ≤ x)
<⇒≱ = ToStrict.<⇒≱ antisym

≤⇒≯ : ∀ {x y} → x ≤ y → ¬ (y < x)
≤⇒≯ = ToStrict.≤⇒≯ antisym


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.2

invIsPartialOrder = ≥-isPartialOrder
{-# WARNING_ON_USAGE invIsPartialOrder
"Warning: invIsPartialOrder was deprecated in v1.2.
Please use ≥-isPartialOrder instead."
#-}

invPoset = ≥-poset
{-# WARNING_ON_USAGE invPoset
"Warning: invPoset was deprecated in v1.2.
Please use ≥-poset instead."
#-}

strictPartialOrder = <-strictPartialOrder
{-# WARNING_ON_USAGE strictPartialOrder
"Warning: strictPartialOrder was deprecated in v1.2.
Please use <-strictPartialOrder instead."
#-}
