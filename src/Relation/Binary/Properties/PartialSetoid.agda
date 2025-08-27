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

partial-reflˡ : x ≈ y → x ≈ x
partial-reflˡ p = trans p (sym p)

partial-reflʳ : x ≈ y → y ≈ y
partial-reflʳ p = trans (sym p) p

partial-refl : x ≈ y → x ≈ x × y ≈ y
partial-refl p = partial-reflˡ p , partial-reflʳ p

partial-reflexiveˡ : x ≈ y → x ≡ z → x ≈ z
partial-reflexiveˡ p ≡.refl = partial-reflˡ p

partial-reflexiveʳ : x ≈ y → y ≡ z → y ≈ z
partial-reflexiveʳ p ≡.refl = partial-reflʳ p

