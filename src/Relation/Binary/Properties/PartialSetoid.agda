------------------------------------------------------------------------
-- The Agda standard library
--
-- Additional properties for setoids
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (PartialSetoid)

module Relation.Binary.Properties.PartialSetoid
  {a ℓ} (S : PartialSetoid a ℓ) where

open import Data.Product.Base using (_,_; _×_)
open import Relation.Binary.Definitions using (LeftTrans; RightTrans)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

open PartialSetoid S

private
  variable
    x y z : Carrier

------------------------------------------------------------------------
-- Proofs for partial equivalence relations

trans-reflˡ : LeftTrans _≡_ _≈_
trans-reflˡ ≡.refl p = p

trans-reflʳ : RightTrans _≈_ _≡_
trans-reflʳ p ≡.refl = p

p-reflˡ : x ≈ y → x ≈ x
p-reflˡ p = trans p (sym p)

p-reflʳ : x ≈ y → y ≈ y
p-reflʳ p = trans (sym p) p

p-refl : x ≈ y → x ≈ x × y ≈ y
p-refl p = p-reflˡ p , p-reflʳ p

p-reflexiveˡ : x ≈ y → x ≡ z → x ≈ z
p-reflexiveˡ p ≡.refl = p-reflˡ p

p-reflexiveʳ : x ≈ y → y ≡ z → y ≈ z
p-reflexiveʳ p ≡.refl = p-reflʳ p

