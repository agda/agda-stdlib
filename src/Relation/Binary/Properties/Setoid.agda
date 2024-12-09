------------------------------------------------------------------------
-- The Agda standard library
--
-- Additional properties for setoids
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Product.Base using (_,_)
open import Function.Base using (_∘_; id; _$_; flip)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Binary.Bundles using (Setoid; Preorder; Poset)
open import Relation.Binary.Definitions
  using (Symmetric; _Respectsˡ_; _Respectsʳ_; _Respects₂_; Irreflexive)
open import Relation.Binary.Structures using (IsPreorder; IsPartialOrder)
open import Relation.Binary.Construct.Composition
  using (_;_; impliesˡ; transitive⇒≈;≈⊆≈)

module Relation.Binary.Properties.Setoid {a ℓ} (S : Setoid a ℓ) where

open Setoid S

------------------------------------------------------------------------
-- Every setoid is a preorder and partial order with respect to
-- propositional equality

isPreorder : IsPreorder _≡_ _≈_
isPreorder = record
  { isEquivalence = record
    { refl  = ≡.refl
    ; sym   = ≡.sym
    ; trans = ≡.trans
    }
  ; reflexive     = reflexive
  ; trans         = trans
  }

≈-isPreorder : IsPreorder _≈_ _≈_
≈-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = id
  ; trans         = trans
  }

≈-isPartialOrder : IsPartialOrder _≈_ _≈_
≈-isPartialOrder = record
  { isPreorder = ≈-isPreorder
  ; antisym    = λ i≈j _ → i≈j
  }

preorder : Preorder a a ℓ
preorder = record
  { isPreorder = isPreorder
  }

≈-preorder : Preorder a ℓ ℓ
≈-preorder = record
  { isPreorder = ≈-isPreorder
  }

≈-poset : Poset a ℓ ℓ
≈-poset = record
  { isPartialOrder = ≈-isPartialOrder
  }

------------------------------------------------------------------------
-- Properties of _≉_

≉-sym :  Symmetric _≉_
≉-sym x≉y =  x≉y ∘ sym

≉-respˡ : _≉_ Respectsˡ _≈_
≉-respˡ x≈x′ x≉y = x≉y ∘ trans x≈x′

≉-respʳ : _≉_ Respectsʳ _≈_
≉-respʳ y≈y′ x≉y x≈y′ = x≉y $ trans x≈y′ (sym y≈y′)

≉-resp₂ : _≉_ Respects₂ _≈_
≉-resp₂ = ≉-respʳ , ≉-respˡ

≉-irrefl : Irreflexive _≈_ _≉_
≉-irrefl x≈y x≉y = contradiction x≈y x≉y

------------------------------------------------------------------------
-- Equality is closed under composition

≈;≈⇒≈ : _≈_ ; _≈_ ⇒ _≈_
≈;≈⇒≈ = transitive⇒≈;≈⊆≈ _ trans

≈⇒≈;≈ : _≈_ ⇒ _≈_ ; _≈_
≈⇒≈;≈ = impliesˡ _≈_ _≈_ refl id

------------------------------------------------------------------------
-- Other properties

respʳ-flip : _≈_ Respectsʳ (flip _≈_)
respʳ-flip y≈z x≈z = trans x≈z (sym y≈z)

respˡ-flip : _≈_ Respectsˡ (flip _≈_)
respˡ-flip = trans
