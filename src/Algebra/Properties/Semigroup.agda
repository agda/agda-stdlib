------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for Semigroup
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semigroup)
import Algebra.Properties.Magma
open import Data.Product using (_,_)
open import Relation.Binary using (Transitive)
import Relation.Binary.Reasoning.Setoid as EqReasoning

module Algebra.Properties.Semigroup {a ℓ} (S : Semigroup a ℓ) where

open Semigroup S
open EqReasoning setoid
open Algebra.Properties.Magma magma public

x∙yz≈xy∙z : ∀ x y z → x ∙ (y ∙ z) ≈ (x ∙ y) ∙ z
x∙yz≈xy∙z x y z = sym (assoc x y z)

∣-trans : Transitive _∣_
∣-trans {x} {y} {z} (p , y≈px) (q , z≈qy) = q ∙ p , (begin
  z              ≈⟨ z≈qy ⟩
  q ∙ y          ≈⟨ ∙-congˡ y≈px ⟩
  q ∙ (p ∙ x)    ≈˘⟨ assoc q p x ⟩
  (q ∙ p) ∙ x    ∎)
