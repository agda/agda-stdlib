------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of divisibility over commutative semigroups
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeSemigroup)
open import Data.Product using (_,_)
import Relation.Binary.Reasoning.Setoid as EqReasoning

module Algebra.Properties.CommutativeSemigroup.Divisibility
  {a ℓ} (CS : CommutativeSemigroup a ℓ)
  where

open CommutativeSemigroup CS
open import Algebra.Properties.CommutativeSemigroup CS using (x∙yz≈xz∙y; x∙yz≈y∙xz)
open EqReasoning setoid

------------------------------------------------------------------------------
-- Re-export the contents of divisibility over semigroups

open import Algebra.Properties.Semigroup.Divisibility semigroup public

------------------------------------------------------------------------------
-- Re-export the contents of divisibility over commutative magmas

open import Algebra.Properties.CommutativeMagma.Divisibility commutativeMagma public
  using (x∣xy; xy≈z⇒x∣z; ∣-factors; ∣-factors-≈)

------------------------------------------------------------------------------
-- New properties

x∣y∧z∣x/y⇒xz∣y : ∀ {x y z} → ((x/y , _) : x ∣ y) → z ∣ x/y → x ∙ z ∣ y
x∣y∧z∣x/y⇒xz∣y {x} {y} {z} (x/y , x/y∙x≈y) (p , pz≈x/y) = p , (begin
  p ∙ (x ∙ z)  ≈⟨ x∙yz≈xz∙y p x z ⟩
  (p ∙ z) ∙ x  ≈⟨ ∙-congʳ pz≈x/y ⟩
  x/y ∙ x      ≈⟨ x/y∙x≈y ⟩
  y            ∎)

x∣y⇒zx∣zy : ∀ {x y} z → x ∣ y → z ∙ x ∣ z ∙ y
x∣y⇒zx∣zy {x} {y} z (q , qx≈y) = q , (begin
 q ∙ (z ∙ x)  ≈⟨ x∙yz≈y∙xz q z x ⟩
 z ∙ (q ∙ x)  ≈⟨ ∙-congˡ qx≈y ⟩
 z ∙ y        ∎)
