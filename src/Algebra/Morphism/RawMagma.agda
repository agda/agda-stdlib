------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences of a morphism between magmas
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Morphism
open RawMagma using (Carrier; _≈_)

module Algebra.Morphism.RawMagma
  {a b ℓ₁ ℓ₂} {From : RawMagma b ℓ₂} {To : RawMagma a ℓ₁}
  {to : Carrier From → Carrier To}
  (isRawMagmaMorphism : IsRawMagmaMorphism From To to)
  (to-injective : ∀ {x y} → _≈_ To (to x) (to y) → _≈_ From x y)
  where

open import Algebra.FunctionProperties
open import Data.Product
open import Data.Sum using (inj₁; inj₂)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Relation.Binary.Reasoning.MultiSetoid as MultiSetoidReasoning

private
  module F = RawMagma From
  module T = RawMagma To

open Definitions F.Carrier T.Carrier T._≈_
open T using () renaming (_∙_ to _⊕_)
open F using (_∙_)

open IsRawMagmaMorphism isRawMagmaMorphism

assoc-homo : Associative T._≈_ _⊕_ → Associative F._≈_ _∙_
assoc-homo assoc x y z = to-injective (begin
  to ((x ∙ y) ∙ z)      ≈⟨  ∙-homo (x ∙ y) z ⟩
  to (x ∙ y) ⊕ to z     ≈⟨  T-∙-congʳ (∙-homo x y) ⟩
  (to x ⊕ to y) ⊕ to z  ≈⟨  assoc (to x) (to y) (to z) ⟩
  to x ⊕ (to y ⊕ to z)  ≈˘⟨ T-∙-congˡ (∙-homo y z) ⟩
  to x ⊕ to (y ∙ z)     ≈˘⟨ ∙-homo x (y ∙ z) ⟩
  to (x ∙ (y ∙ z))      ∎)
  where open SetoidReasoning T-setoid

comm-homo : Commutative T._≈_ _⊕_ → Commutative F._≈_ _∙_
comm-homo comm x y = to-injective (begin
  to (x ∙ y)    ≈⟨  ∙-homo x y ⟩
  to x ⊕ to y   ≈⟨  comm (to x) (to y) ⟩
  to y ⊕ to x   ≈˘⟨ ∙-homo y x ⟩
  to (y ∙ x)    ∎)
  where open SetoidReasoning T-setoid

idem-homo : Idempotent T._≈_ _⊕_ → Idempotent F._≈_ _∙_
idem-homo idem x = to-injective (begin
  to (x ∙ x)  ≈⟨ ∙-homo x x ⟩
  to x ⊕ to x ≈⟨ idem (to x) ⟩
  to x        ∎)
  where open SetoidReasoning T-setoid

sel-homo : Selective T._≈_ _⊕_ → Selective F._≈_ _∙_
sel-homo sel x y with sel (to x) (to y)
... | inj₁ x⊕y≈x = inj₁ (to-injective (begin
  to (x ∙ y)   ≈⟨ ∙-homo x y ⟩
  to x ⊕ to y  ≈⟨ x⊕y≈x ⟩
  to x         ∎))
  where open SetoidReasoning T-setoid
... | inj₂ x⊕y≈y = inj₂ (to-injective (begin
  to (x ∙ y)   ≈⟨ ∙-homo x y ⟩
  to x ⊕ to y  ≈⟨ x⊕y≈y ⟩
  to y         ∎))
  where open SetoidReasoning T-setoid

cancelˡ-homo : LeftCancellative T._≈_ _⊕_ → LeftCancellative F._≈_ _∙_
cancelˡ-homo cancelˡ x {y} {z} x∙y≈x∙z = to-injective (cancelˡ (to x) (begin
  to x ⊕ to y ≈˘⟨ ∙-homo x y ⟩
  to (x ∙ y)  ≈⟨ ⟦⟧-cong x∙y≈x∙z ⟩
  to (x ∙ z)  ≈⟨  ∙-homo x z ⟩
  to x ⊕ to z ∎))
  where open SetoidReasoning T-setoid

cancelʳ-homo : RightCancellative T._≈_ _⊕_ → RightCancellative F._≈_ _∙_
cancelʳ-homo cancelʳ {x} y z y∙x≈z∙x = to-injective (cancelʳ (to y) (to z) (begin
  to y ⊕ to x ≈˘⟨ ∙-homo y x ⟩
  to (y ∙ x)  ≈⟨ ⟦⟧-cong y∙x≈z∙x ⟩
  to (z ∙ x)  ≈⟨  ∙-homo z x ⟩
  to z ⊕ to x ∎))
  where open SetoidReasoning T-setoid

cancel-homo : Cancellative T._≈_ _⊕_ → Cancellative F._≈_ _∙_
cancel-homo (cancelˡ , cancelʳ) = cancelˡ-homo cancelˡ , cancelʳ-homo cancelʳ
