------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic properties of the function type
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Properties where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Function.Base using (id; flip; _∘_; _∘′_)
open import Function.Bundles using (_↔_; mk↔ₛ′; Inverse)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.Bundles
  using (Poset)
open import Relation.Binary.Construct.Interior.Symmetric
  using (SymInterior; poset)
open import Relation.Binary.Core using (REL; Rel)
open import Relation.Binary.Definitions
  using (Reflexive; Trans; Transitive)
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
Π↔Π = mk↔ₛ′ (λ f {x} → f x) (λ f _ → f) cong′ cong′

------------------------------------------------------------------------
-- Function spaces can be reordered

ΠΠ↔ΠΠ : (R : A → B → Set p) →
        ((x : A) (y : B) → R x y) ↔ ((y : B) (x : A) → R x y)
ΠΠ↔ΠΠ _ = mk↔ₛ′ flip flip cong′ cong′

------------------------------------------------------------------------
-- Assuming extensionality then → preserves ↔

→-cong-↔ : {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
         Extensionality a c → Extensionality b d →
         A ↔ B → C ↔ D → (A → C) ↔ (B → D)
→-cong-↔ extAC extBD A↔B C↔D = mk↔ₛ′
  (λ h → C↔D.to   ∘ h ∘ A↔B.from)
  (λ g → C↔D.from ∘ g ∘ A↔B.to  )
  (λ h → extBD λ x → trans (C↔D.strictlyInverseˡ _) (cong h (A↔B.strictlyInverseˡ x)))
  (λ g → extAC λ x → trans (C↔D.strictlyInverseʳ _) (cong g (A↔B.strictlyInverseʳ x)))
  where module A↔B = Inverse A↔B; module C↔D = Inverse C↔D

------------------------------------------------------------------------
-- _→_ defines a PartialOrder

module _ where

  private
    Arrow : REL (Set a) (Set b) (a ⊔ b)
    Arrow A B = A → B

  →-refl : Reflexive {A = Set a} Arrow
  →-refl = id

  →-trans : Trans {A = Set a} {B = Set b} {C = Set c} Arrow Arrow Arrow
  →-trans = flip _∘′_

module _ {a} where

  private
    Arrow′ : Rel (Set a) a
    Arrow′ S T = S → T

  →-refl′ : Reflexive Arrow′
  →-refl′ = id

  →-trans′ : Transitive Arrow′
  →-trans′ = flip _∘′_

  →-poset : Poset (suc a) _ _
  →-poset = poset (λ {x = S} → →-refl′ {x = S}) →-trans′

  open Poset →-poset public
    using (isPartialOrder; isPreorder; isEquivalence)
