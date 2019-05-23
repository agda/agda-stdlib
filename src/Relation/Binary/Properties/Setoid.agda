------------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for Setoid
------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


open import Relation.Binary using (Rel; Symmetric; _Respects_; _Respects2_;
                                                               Setoid)


module Relation.Binary.Properties.Setoid {ℓ ℓ=} (A : Setoid ℓ ℓ=) where

open import Function         using (_∘_)
open import Relation.Nullary using (¬_)

open Setoid A using (Carrier; _≈_; refl; sym; trans)

_≉_ :  Rel Carrier _
_≉_ x =  ¬_ ∘ (x ≈_)

≉sym :  Symmetric _≉_
≉sym {x} {y} x≉y =  x≉y ∘ sym

≉resp :  _≉_ Respects2 _≈_                           -- ... x ≉ y → x' ≉ y'
≉resp {x} {x'} {y} {y'} x=x' y=y' x≉y x'=y' =  x≉y x=y
  where
  x=y =  trans (trans x=x' x'=y') (sym y=y')

≉respˡ :  {y : Carrier} → (_≉ y) Respects _≈_
≉respˡ x=x' =  ≉resp x=x' refl

≉respʳ :  {x : Carrier} → (x ≉_) Respects _≈_
≉respʳ =  ≉resp refl
