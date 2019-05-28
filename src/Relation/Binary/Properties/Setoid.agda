------------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for Setoid
------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


open import Relation.Binary using (Rel; Symmetric; _Respectsˡ_; _Respectsʳ_;
                                                               Setoid)


module Relation.Binary.Properties.Setoid {ℓ ℓ=} (A : Setoid ℓ ℓ=) where

open import Function         using (_∘_; _$_)
open import Relation.Nullary using (¬_)

open Setoid A using (Carrier; _≈_; refl; sym; trans)

_≉_ :  Rel Carrier _
_≉_ x =  ¬_ ∘ (x ≈_)

≉-sym :  Symmetric _≉_
≉-sym {x} {y} x≉y =  x≉y ∘ sym

≉-respˡ : _≉_ Respectsˡ _≈_
≉-respˡ {y} {x} {x'} x≈x' x≉y =  x≉y ∘ trans x≈x'

≉-respʳ : _≉_ Respectsʳ _≈_
≉-respʳ {x} {y} {y'} y≈y' x≉y =  (\x≈y' → x≉y $ trans x≈y' (sym y≈y'))

