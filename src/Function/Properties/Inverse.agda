------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of inverses.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Properties.Inverse where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Function.Bundles
import Function.Properties.RightInverse as RightInverse using (to-from)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (REL)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Function.Consequences.Setoid as Consequences
  using (inverseʳ⇒injective; inverseˡ⇒surjective; inverseᵇ⇒bijective)

import Function.Construct.Identity as Identity
import Function.Construct.Symmetry as Symmetry
import Function.Construct.Composition as Composition

private
  variable
    a b ℓ ℓ₁ ℓ₂ : Level
    A B C D : Set a
    S T U V : Setoid a ℓ


------------------------------------------------------------------------
-- Setoid bundles

open Identity    public using () renaming (inverse to refl)
open Symmetry    public using () renaming (inverse to sym)
open Composition public using () renaming (inverse to trans)

isEquivalence : IsEquivalence (Inverse {a} {b})
isEquivalence = record
  { refl  = λ {x} → Identity.inverse x
  ; sym   = sym
  ; trans = trans
  }

------------------------------------------------------------------------
-- Propositional bundles

↔-refl : A ↔ A
↔-refl = Identity.↔-id _

↔-sym : A ↔ B → B ↔ A
↔-sym = Symmetry.↔-sym

↔-trans : A ↔ B → B ↔ C → A ↔ C
↔-trans = Composition.inverse

-- need to η-expand for everything to line up properly
↔-isEquivalence : IsEquivalence {ℓ = ℓ} _↔_
↔-isEquivalence = record
  { refl  = ↔-refl
  ; sym   = ↔-sym
  ; trans = ↔-trans
  }

------------------------------------------------------------------------
-- Conversion functions

module _ (I : Inverse S T) where

  open Inverse I
  open Consequences S T

  Inverse⇒Injection : Injection S T
  Inverse⇒Injection = record
    { Func toFunction
    ; injective = inverseʳ⇒injective to inverseʳ
    }

  Inverse⇒Surjection : Surjection S T
  Inverse⇒Surjection = record
    { Func toFunction
    ; surjective = inverseˡ⇒surjective inverseˡ
    }

  Inverse⇒Bijection : Bijection S T
  Inverse⇒Bijection = record
    { Func toFunction
    ; bijective = inverseᵇ⇒bijective inverse
    }

  Inverse⇒Equivalence : Equivalence S T
  Inverse⇒Equivalence = equivalence

↔⇒⟶ : A ↔ B → A ⟶ B
↔⇒⟶ = Inverse.toFunction

↔⇒⟵ : A ↔ B → B ⟶ A
↔⇒⟵ = Inverse.fromFunction

↔⇒↣ : A ↔ B → A ↣ B
↔⇒↣ = Inverse⇒Injection

↔⇒↠ : A ↔ B → A ↠ B
↔⇒↠ = Inverse⇒Surjection

↔⇒⤖ : A ↔ B → A ⤖ B
↔⇒⤖ = Inverse⇒Bijection

↔⇒⇔ : A ↔ B → A ⇔ B
↔⇒⇔ = Inverse.equivalence

↔⇒↩ : A ↔ B → A ↩ B
↔⇒↩ = Inverse.leftInverse

↔⇒↪ : A ↔ B → A ↪ B
↔⇒↪ = Inverse.rightInverse

-- The functions above can be combined with the following lemma to
-- transport an arbitrary relation R (e.g. Injection) across
-- inverses.
transportVia : {R : ∀ {a b ℓ₁ ℓ₂} → REL (Setoid a ℓ₁) (Setoid b ℓ₂) (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)} →
               (∀ {a b c ℓ₁ ℓ₂ ℓ₃} {S : Setoid a ℓ₁} {T : Setoid b ℓ₂} {U : Setoid c ℓ₃} → R S T → R T U → R S U) →
               (∀ {a b ℓ₁ ℓ₂} {S : Setoid a ℓ₁} {T : Setoid b ℓ₂} → Inverse S T → R S T) →
               Inverse S T → R T U → Inverse U V → R S V
transportVia R-trans inv⇒R IBA RBC ICD =
  R-trans (inv⇒R IBA) (R-trans RBC (inv⇒R ICD))

------------------------------------------------------------------------
-- Other

module _ (ext : ∀ {a b} → Extensionality a b) where

  ↔-fun : A ↔ B → C ↔ D → (A → C) ↔ (B → D)
  ↔-fun A↔B C↔D = mk↔ₛ′
    (λ a→c b → to C↔D (a→c (from A↔B b)))
    (λ b→d a → from C↔D (b→d (to A↔B a)))
    (λ b→d → ext λ _ → ≡.trans (strictlyInverseˡ C↔D _ ) (≡.cong b→d (strictlyInverseˡ A↔B _)))
    (λ a→c → ext λ _ → ≡.trans (strictlyInverseʳ C↔D _ ) (≡.cong a→c (strictlyInverseʳ A↔B _)))
    where open Inverse

module _ (I : Inverse S T) where
  open Inverse I

  to-from : ∀ {x y} → to x Eq₂.≈ y → from y Eq₁.≈ x
  to-from = RightInverse.to-from rightInverse


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 3.0

module _ (I : Inverse S T) where
  open Inverse I public
    using (toFunction; fromFunction)

{-# WARNING_ON_USAGE toFunction
"Warning: toFunction was deprecated in v3.0.
Please use Inverse.toFunction, directly exported from the bundle, instead."
#-}
{-# WARNING_ON_USAGE fromFunction
"Warning: fromFunction was deprecated in v3.0.
Please use Inverse.fromFunction, directly exported from the bundle, instead."
#-}

