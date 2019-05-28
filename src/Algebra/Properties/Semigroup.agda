------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for Semigroup
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semigroup)

module Algebra.Properties.Semigroup
       {ℓ ℓ=} (H : Semigroup ℓ ℓ=) (open Semigroup H using (_≈_; _∙_)) where

open Semigroup H using (sym; assoc)

x∙yz≈xy∙z :  ∀ x y z → x ∙ (y ∙ z) ≈ (x ∙ y) ∙ z
x∙yz≈xy∙z x y z =  sym (assoc x y z)
