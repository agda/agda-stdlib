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
∣-trans {x} {y} {z} (q , y≈qx) (q' , z≈q'y) = (q' ∙ q , z≈q'qx)
 where
 z≈q'qx = begin
   z              ≈⟨ z≈q'y ⟩
   q' ∙ y         ≈⟨ ∙-congˡ y≈qx ⟩
   q' ∙ (q ∙ x)   ≈⟨ sym (assoc q' q x) ⟩
   (q' ∙ q) ∙ x   ∎

