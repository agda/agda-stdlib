------------------------------------------------------------------------------
-- The Agda standard library
--
-- Additional properties for setoids
------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Properties.Setoid {a ℓ} (S : Setoid a ℓ) where

open import Function using (_∘_; _$_)
open import Relation.Nullary using (¬_)

open Setoid S using (Carrier; _≈_; refl; sym; trans)

_≉_ :  Rel Carrier _
_≉_ x =  ¬_ ∘ (x ≈_)

≉-sym :  Symmetric _≉_
≉-sym {x} {y} x≉y =  x≉y ∘ sym

≉-respˡ : _≉_ Respectsˡ _≈_
≉-respˡ {y} {x} {x'} x≈x' x≉y = x≉y ∘ trans x≈x'

≉-respʳ : _≉_ Respectsʳ _≈_
≉-respʳ {x} {y} {y'} y≈y' x≉y = (λ x≈y' → x≉y $ trans x≈y' (sym y≈y'))

