------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of divisibility over commutative semigroups
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeSemigroup)

module Algebra.Properties.CommutativeSemigroup.Divisibility
  {a ℓ} (commutativeSemigroup : CommutativeSemigroup a ℓ)
  where

open import Data.Product.Base using (_,_)

open CommutativeSemigroup commutativeSemigroup
open import Algebra.Properties.CommutativeSemigroup commutativeSemigroup
  using (medial; x∙yz≈xz∙y; x∙yz≈y∙xz)
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Re-export the contents of divisibility over semigroups

open import Algebra.Properties.Semigroup.Divisibility semigroup public

------------------------------------------------------------------------
-- Re-export the contents of divisibility over commutative magmas

open import Algebra.Properties.CommutativeMagma.Divisibility commutativeMagma public
  using (x∣xy; xy≈z⇒x∣z; ∣-factors; ∣-factors-≈)

------------------------------------------------------------------------
-- New properties

x∣y∧z∣x/y⇒xz∣y : ∀ {x y z} → ((x/y , _) : x ∣ y) → z ∣ x/y → x ∙ z ∣ y
x∣y∧z∣x/y⇒xz∣y {x} {y} {z} (x/y , x/y∙x≈y) (p , pz≈x/y) = p , (begin
  p ∙ (x ∙ z)  ≈⟨ x∙yz≈xz∙y p x z ⟩
  (p ∙ z) ∙ x  ≈⟨ ∙-congʳ pz≈x/y ⟩
  x/y ∙ x      ≈⟨ x/y∙x≈y ⟩
  y            ∎)

∙-cong-∣ : ∀ {x y a b} → x ∣ y → a ∣ b → x ∙ a ∣ y ∙ b
∙-cong-∣ {x} {y} {a} {b} (p , px≈y) (q , qa≈b) = p ∙ q , (begin
  (p ∙ q) ∙ (x ∙ a) ≈⟨ medial p q x a ⟩
  (p ∙ x) ∙ (q ∙ a) ≈⟨ ∙-cong px≈y qa≈b ⟩
  y ∙ b ∎)

x∣y⇒zx∣zy : ∀ {x y} z → x ∣ y → z ∙ x ∣ z ∙ y
x∣y⇒zx∣zy {x} {y} z (q , qx≈y) = q , (begin
 q ∙ (z ∙ x)  ≈⟨ x∙yz≈y∙xz q z x ⟩
 z ∙ (q ∙ x)  ≈⟨ ∙-congˡ qx≈y ⟩
 z ∙ y        ∎)
