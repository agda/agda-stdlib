------------------------------------------------------------------------------
-- The Agda standard library
--
-- Additional properties for setoids
------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Product using (_,_)
open import Function.Base using (_∘_; _$_; flip)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Binary

module Relation.Binary.Properties.Setoid {a ℓ} (S : Setoid a ℓ) where

open Setoid S


------------------------------------------------------------------------------
-- Every setoid is a preorder with respect to propositional equality

isPreorder : IsPreorder _≡_ _≈_
isPreorder = record
  { isEquivalence = P.isEquivalence
  ; reflexive     = reflexive
  ; trans         = trans
  }

preorder : Preorder a a ℓ
preorder = record
  { isPreorder = isPreorder
  }

------------------------------------------------------------------------------
-- Properties of _≉_

≉-sym :  Symmetric _≉_
≉-sym x≉y =  x≉y ∘ sym

≉-respˡ : _≉_ Respectsˡ _≈_
≉-respˡ x≈x′ x≉y = x≉y ∘ trans x≈x′

≉-respʳ : _≉_ Respectsʳ _≈_
≉-respʳ y≈y′ x≉y x≈y′ = x≉y $ trans x≈y′ (sym y≈y′)

≉-resp₂ : _≉_ Respects₂ _≈_
≉-resp₂ = ≉-respʳ , ≉-respˡ

------------------------------------------------------------------------------
-- Other properties

respʳ-flip : _≈_ Respectsʳ (flip _≈_)
respʳ-flip y≈z x≈z = trans x≈z (sym y≈z)

respˡ-flip : _≈_ Respectsˡ (flip _≈_)
respˡ-flip = trans
