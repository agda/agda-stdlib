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
  {from : Carrier To → Carrier From}
  (from-to : ∀ x → _≈_ From (from (to x)) x)
  (from-cong : ∀ {x y} → _≈_ To x y → _≈_ From (from x) (from y))
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
assoc-homo assoc x y z = begin
  (x ∙ y) ∙ z                 ≈˘⟨ from-to ((x ∙ y) ∙ z) ⟩
  from (to ((x ∙ y) ∙ z))     ≈⟨  from-cong (∙-homo (x ∙ y) z) ⟩
  from (to (x ∙ y) ⊕ to z)    ≈⟨  from-cong (T-∙-congʳ (∙-homo x y)) ⟩
  from ((to x ⊕ to y) ⊕ to z) ≈⟨  from-cong (assoc (to x) (to y) (to z)) ⟩
  from (to x ⊕ (to y ⊕ to z)) ≈˘⟨ from-cong (T-∙-congˡ (∙-homo y z)) ⟩
  from (to x ⊕ to (y ∙ z))    ≈˘⟨ from-cong (∙-homo x (y ∙ z)) ⟩
  from (to (x ∙ (y ∙ z)))     ≈⟨  from-to (x ∙ (y ∙ z)) ⟩
  (x ∙ (y ∙ z))               ∎
  where open SetoidReasoning F-setoid

comm-homo : Commutative T._≈_ _⊕_ → Commutative F._≈_ _∙_
comm-homo comm x y = begin
  x ∙ y                ≈˘⟨ from-to (x ∙ y) ⟩
  from (to (x ∙ y))    ≈⟨  from-cong (∙-homo x y) ⟩
  from (to x ⊕ to y)   ≈⟨  from-cong (comm (to x) (to y)) ⟩
  from (to y ⊕ to x)   ≈˘⟨ from-cong (∙-homo y x) ⟩
  from (to (y ∙ x))    ≈⟨  from-to (y ∙ x) ⟩
  y ∙ x                ∎
  where open SetoidReasoning F-setoid

idem-homo : Idempotent T._≈_ _⊕_ → Idempotent F._≈_ _∙_
idem-homo idem x = begin
  x ∙ x              ≈˘⟨ from-to (x ∙ x) ⟩
  from (to (x ∙ x))  ≈⟨ from-cong (∙-homo x x) ⟩
  from (to x ⊕ to x) ≈⟨ from-cong (idem (to x)) ⟩
  from (to x)        ≈⟨ from-to x ⟩
  x                  ∎
  where open SetoidReasoning F-setoid

sel-homo : Selective T._≈_ _⊕_ → Selective F._≈_ _∙_
sel-homo sel x y with sel (to x) (to y)
... | inj₁ x⊕y≈x = inj₁ (begin
  x ∙ y               ≈˘⟨ from-to (x ∙ y) ⟩
  from (to (x ∙ y))   ≈⟨ from-cong (∙-homo x y) ⟩
  from (to x ⊕ to y)  ≈⟨ from-cong x⊕y≈x ⟩
  from (to x)         ≈⟨ from-to x ⟩
  x                   ∎)
  where open SetoidReasoning F-setoid
... | inj₂ x⊕y≈y = inj₂ (begin
  x ∙ y               ≈˘⟨ from-to (x ∙ y) ⟩
  from (to (x ∙ y))   ≈⟨ from-cong (∙-homo x y) ⟩
  from (to x ⊕ to y)  ≈⟨ from-cong x⊕y≈y ⟩
  from (to y)         ≈⟨ from-to y ⟩
  y                   ∎)
  where open SetoidReasoning F-setoid

cancelˡ-homo : LeftCancellative T._≈_ _⊕_ → LeftCancellative F._≈_ _∙_
cancelˡ-homo cancelˡ x {y} {z} x∙y≈x∙z = begin⟨ F-setoid ⟩
  y           ≈˘⟨ from-to y ⟩
  from (to y) ≈⟨ from-cong (cancelˡ (to x) (begin⟨ T-setoid ⟩
    to x ⊕ to y ≈˘⟨ ∙-homo x y ⟩
    to (x ∙ y)  ≈⟨ ⟦⟧-cong x∙y≈x∙z ⟩
    to (x ∙ z)  ≈⟨  ∙-homo x z ⟩
    to x ⊕ to z ∎)) ⟩
  from (to z) ≈⟨  from-to z ⟩
  z           ∎
  where open MultiSetoidReasoning

cancelʳ-homo : RightCancellative T._≈_ _⊕_ → RightCancellative F._≈_ _∙_
cancelʳ-homo cancelʳ {x} y z y∙x≈z∙x = begin⟨ F-setoid ⟩
  y           ≈˘⟨ from-to y ⟩
  from (to y) ≈⟨ from-cong (cancelʳ (to y) (to z) (begin⟨ T-setoid ⟩
    to y ⊕ to x ≈˘⟨ ∙-homo y x ⟩
    to (y ∙ x)  ≈⟨ ⟦⟧-cong y∙x≈z∙x ⟩
    to (z ∙ x)  ≈⟨  ∙-homo z x ⟩
    to z ⊕ to x ∎)) ⟩
  from (to z) ≈⟨  from-to z ⟩
  z           ∎
  where open MultiSetoidReasoning

cancel-homo : Cancellative T._≈_ _⊕_ → Cancellative F._≈_ _∙_
cancel-homo (cancelˡ , cancelʳ) = cancelˡ-homo cancelˡ , cancelʳ-homo cancelʳ
