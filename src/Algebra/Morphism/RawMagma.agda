------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences of an injective morphism between magmas
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Morphism
open import Function
open RawMagma using (Carrier; _≈_)

module Algebra.Morphism.RawMagma
  {a b ℓ₁ ℓ₂} {From : RawMagma b ℓ₂} {To : RawMagma a ℓ₁}
  {f : Carrier From → Carrier To}
  (f-isRawMagmaMorphism : IsRawMagmaMorphism From To f)
  (f-injective : Injective (_≈_ From) (_≈_ To) f)
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

open IsRawMagmaMorphism f-isRawMagmaMorphism
open SetoidReasoning T-setoid

assoc-homo : Associative T._≈_ _⊕_ → Associative F._≈_ _∙_
assoc-homo assoc x y z = f-injective (begin
  f ((x ∙ y) ∙ z)    ≈⟨  ∙-homo (x ∙ y) z ⟩
  f (x ∙ y) ⊕ f z    ≈⟨  T-∙-congʳ (∙-homo x y) ⟩
  (f x ⊕ f y) ⊕ f z  ≈⟨  assoc (f x) (f y) (f z) ⟩
  f x ⊕ (f y ⊕ f z)  ≈˘⟨ T-∙-congˡ (∙-homo y z) ⟩
  f x ⊕ f (y ∙ z)    ≈˘⟨ ∙-homo x (y ∙ z) ⟩
  f (x ∙ (y ∙ z))    ∎)

comm-homo : Commutative T._≈_ _⊕_ → Commutative F._≈_ _∙_
comm-homo comm x y = f-injective (begin
  f (x ∙ y)  ≈⟨  ∙-homo x y ⟩
  f x ⊕ f y  ≈⟨  comm (f x) (f y) ⟩
  f y ⊕ f x  ≈˘⟨ ∙-homo y x ⟩
  f (y ∙ x)  ∎)

idem-homo : Idempotent T._≈_ _⊕_ → Idempotent F._≈_ _∙_
idem-homo idem x = f-injective (begin
  f (x ∙ x)  ≈⟨ ∙-homo x x ⟩
  f x ⊕ f x  ≈⟨ idem (f x) ⟩
  f x        ∎)

sel-homo : Selective T._≈_ _⊕_ → Selective F._≈_ _∙_
sel-homo sel x y with sel (f x) (f y)
... | inj₁ x⊕y≈x = inj₁ (f-injective (begin
  f (x ∙ y)  ≈⟨ ∙-homo x y ⟩
  f x ⊕ f y  ≈⟨ x⊕y≈x ⟩
  f x        ∎))
... | inj₂ x⊕y≈y = inj₂ (f-injective (begin
  f (x ∙ y)  ≈⟨ ∙-homo x y ⟩
  f x ⊕ f y  ≈⟨ x⊕y≈y ⟩
  f y        ∎))

cancelˡ-homo : LeftCancellative T._≈_ _⊕_ → LeftCancellative F._≈_ _∙_
cancelˡ-homo cancelˡ x {y} {z} x∙y≈x∙z = f-injective (cancelˡ (f x) (begin
  f x ⊕ f y  ≈˘⟨ ∙-homo x y ⟩
  f (x ∙ y)  ≈⟨ ⟦⟧-cong x∙y≈x∙z ⟩
  f (x ∙ z)  ≈⟨  ∙-homo x z ⟩
  f x ⊕ f z  ∎))

cancelʳ-homo : RightCancellative T._≈_ _⊕_ → RightCancellative F._≈_ _∙_
cancelʳ-homo cancelʳ {x} y z y∙x≈z∙x = f-injective (cancelʳ (f y) (f z) (begin
  f y ⊕ f x  ≈˘⟨ ∙-homo y x ⟩
  f (y ∙ x)  ≈⟨ ⟦⟧-cong y∙x≈z∙x ⟩
  f (z ∙ x)  ≈⟨  ∙-homo z x ⟩
  f z ⊕ f x  ∎))

cancel-homo : Cancellative T._≈_ _⊕_ → Cancellative F._≈_ _∙_
cancel-homo (cancelˡ , cancelʳ) = cancelˡ-homo cancelˡ , cancelʳ-homo cancelʳ
