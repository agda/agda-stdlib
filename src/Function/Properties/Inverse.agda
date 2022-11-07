------------------------------------------------------------------------
-- The Agda standard library
--
-- Some functional properties are Equivalence Relations
--   This file is meant to be imported qualified.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Properties.Inverse where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function.Bundles
open import Level using (Level; _⊔_)
open import Relation.Binary using (REL; Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as P using (setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Function.Consequences

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

-- need to η-expand for everything to line up properly
↔-isEquivalence : IsEquivalence {ℓ = ℓ} _↔_
↔-isEquivalence = record
  { refl  = λ {x} → Identity.inverse (P.setoid x)
  ; sym   = Symmetry.inverse
  ; trans = Composition.inverse
  }

module _ {ℓ} where
  open IsEquivalence (↔-isEquivalence {ℓ}) public
    using ()
    renaming (refl to ↔-refl; sym to ↔-sym; trans to ↔-trans)

------------------------------------------------------------------------
-- Conversion functions

toFunction : Inverse S T → Func S T
toFunction I = record { to = to ; cong = to-cong }
  where open Inverse I

fromFunction : Inverse S T → Func T S
fromFunction I = record { to = from ; cong = from-cong }
  where open Inverse I

Inverse⇒Injection : Inverse S T → Injection S T
Inverse⇒Injection {S = S} I = record
  { to = to
  ; cong = to-cong
  ; injective = inverseʳ⇒injective S {f⁻¹ = from} from-cong inverseʳ
  } where open Inverse I

Inverse⇒Surjection : Inverse S T → Surjection S T
Inverse⇒Surjection {S = S} {T = T} I = record
  { to = to
  ; cong = to-cong
  ; surjective = inverseˡ⇒surjective (_≈_ S) (_≈_ T) inverseˡ
  } where open Inverse I; open Setoid

Inverse⇒Bijection : Inverse S T → Bijection S T
Inverse⇒Bijection {S = S} I = record
  { to        = to
  ; cong      = to-cong
  ; bijective = inverseᵇ⇒bijective S from-cong inverse
  } where open Inverse I

Inverse⇒Equivalence : Inverse S T → Equivalence S T
Inverse⇒Equivalence I = record
  { to        = to
  ; from      = from
  ; to-cong   = to-cong
  ; from-cong = from-cong
  } where open Inverse I

↔⇒↣ : A ↔ B → A ↣ B
↔⇒↣ = Inverse⇒Injection

↔⇒↠ : A ↔ B → A ↠ B
↔⇒↠ = Inverse⇒Surjection

↔⇒⤖ : A ↔ B → A ⤖ B
↔⇒⤖ = Inverse⇒Bijection

↔⇒⇔ : A ↔ B → A ⇔ B
↔⇒⇔ = Inverse⇒Equivalence

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
  ↔-fun A↔B C↔D = mk↔′
    (λ a→c b → to C↔D (a→c (from A↔B b)))
    (λ b→d a → from C↔D (b→d (to A↔B a)))
    (λ b→d → ext λ _ → P.trans (inverseˡ C↔D _ ) (P.cong b→d (inverseˡ A↔B _)))
    (λ a→c → ext λ _ → P.trans (inverseʳ C↔D _ ) (P.cong a→c (inverseʳ A↔B _)))
    where open Inverse
