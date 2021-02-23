------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic properties of the function type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Properties where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Function
open import Level
open import Relation.Binary.PropositionalEquality.Core
  using (trans; cong; cong′)

private
  variable
    a b c d p : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Implicit and explicit function spaces are isomorphic

Π↔Π : {B : A → Set b} → ((x : A) → B x) ↔ ({x : A} → B x)
Π↔Π = mk↔′ (λ f {x} → f x) (λ f _ → f) cong′ cong′

------------------------------------------------------------------------
-- Function spaces can be reordered

ΠΠ↔ΠΠ : (R : A → B → Set p) →
        ((x : A) (y : B) → R x y) ↔ ((y : B) (x : A) → R x y)
ΠΠ↔ΠΠ _ = mk↔′ flip flip cong′ cong′

------------------------------------------------------------------------
-- Assuming extensionality then → preserves ↔

→-cong-↔ : {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
         Extensionality a c → Extensionality b d →
         A ↔ B → C ↔ D → (A → C) ↔ (B → D)
→-cong-↔ extAC extBD A↔B C↔D = mk↔′
  (λ h → C↔D.f   ∘ h ∘ A↔B.f⁻¹)
  (λ g → C↔D.f⁻¹ ∘ g ∘ A↔B.f  )
  (λ h → extBD λ x → trans (C↔D.inverseˡ _) (cong h (A↔B.inverseˡ x)))
  (λ g → extAC λ x → trans (C↔D.inverseʳ _) (cong g (A↔B.inverseʳ x)))
  where module A↔B = Inverse A↔B; module C↔D = Inverse C↔D
