------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by posets
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (Poset; StrictPartialOrder)

module Relation.Binary.Properties.Poset
   {p₁ p₂ p₃} (P : Poset p₁ p₂ p₃) where

open import Data.Product.Base using (_,_)
open import Function.Base using (flip; _∘_)
open import Relation.Binary.Core using (Rel; _Preserves_⟶_)
import Relation.Binary.Consequences as Consequences
  using (mono⇒cong; antimono⇒cong)
open import Relation.Binary.Definitions
  using (_Respectsˡ_; _Respectsʳ_; Decidable)
open import Relation.Binary.Structures
  using (IsPartialOrder; IsStrictPartialOrder; IsDecPartialOrder)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)

open Poset P renaming (Carrier to A)

import Relation.Binary.Construct.NonStrictToStrict _≈_ _≤_ as ToStrict
import Relation.Binary.Properties.Preorder preorder as PreorderProperties


------------------------------------------------------------------------
-- The _≥_ relation is also a poset.

open PreorderProperties public
  using () renaming
  ( converse-isPreorder to ≥-isPreorder
  ; converse-preorder   to ≥-preorder
  )

≥-isPartialOrder : IsPartialOrder _≈_ _≥_
≥-isPartialOrder = record
  { isPreorder   = ≥-isPreorder
  ; antisym      = flip antisym
  }

≥-poset : Poset p₁ p₂ p₃
≥-poset = record
  { isPartialOrder = ≥-isPartialOrder
  }

open Poset ≥-poset public
  using () renaming
  ( refl      to ≥-refl
  ; reflexive to ≥-reflexive
  ; trans     to ≥-trans
  ; antisym   to ≥-antisym
  )

------------------------------------------------------------------------
-- Negated order

≰-respˡ-≈ : _≰_ Respectsˡ _≈_
≰-respˡ-≈ x≈y = _∘ ≤-respˡ-≈ (Eq.sym x≈y)

≰-respʳ-≈ : _≰_ Respectsʳ _≈_
≰-respʳ-≈ x≈y = _∘ ≤-respʳ-≈ (Eq.sym x≈y)

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
  using (_≮_; <-resp-≈; <-respʳ-≈; <-respˡ-≈)
  renaming
  ( irrefl to <-irrefl
  ; asym   to <-asym
  ; trans  to <-trans
  )

<⇒≉ : ∀ {x y} → x < y → x ≉ y
<⇒≉ = ToStrict.<⇒≉

≤∧≉⇒< : ∀ {x y} → x ≤ y → x ≉ y → x < y
≤∧≉⇒< = ToStrict.≤∧≉⇒<

<⇒≱ : ∀ {x y} → x < y → y ≰ x
<⇒≱ = ToStrict.<⇒≱ antisym

≤⇒≯ : ∀ {x y} → x ≤ y → y ≮ x
≤⇒≯ = ToStrict.≤⇒≯ antisym

------------------------------------------------------------------------
-- If ≤ is decidable then so is ≈

≤-dec⇒≈-dec : Decidable _≤_ → Decidable _≈_
≤-dec⇒≈-dec _≤?_ x y with x ≤? y | y ≤? x
... | yes x≤y | yes y≤x = yes (antisym x≤y y≤x)
... | yes x≤y | no  y≰x = no λ x≈y → contradiction (reflexive (Eq.sym x≈y)) y≰x
... | no  x≰y | _       = no λ x≈y → contradiction (reflexive x≈y) x≰y

≤-dec⇒isDecPartialOrder : Decidable _≤_ → IsDecPartialOrder _≈_ _≤_
≤-dec⇒isDecPartialOrder _≤?_ = record
  { isPartialOrder = isPartialOrder
  ; _≟_            = ≤-dec⇒≈-dec _≤?_
  ; _≤?_           = _≤?_
  }

------------------------------------------------------------------------
-- Other properties

mono⇒cong : ∀ {f} → f Preserves _≤_ ⟶ _≤_ → f Preserves _≈_ ⟶ _≈_
mono⇒cong = Consequences.mono⇒cong _≈_ _≈_ Eq.sym reflexive antisym

antimono⇒cong : ∀ {f} → f Preserves _≤_ ⟶ _≥_ → f Preserves _≈_ ⟶ _≈_
antimono⇒cong = Consequences.antimono⇒cong _≈_ _≈_ Eq.sym reflexive antisym
