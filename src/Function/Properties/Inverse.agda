------------------------------------------------------------------------
-- The Agda standard library
--
-- Some functional properties are Equivalence Relations
--   This file is meant to be imported qualified.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Properties.Inverse where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Function.Bundles
open import Level using (Level)
open import Relation.Binary using (Setoid; IsEquivalence)
import Relation.Binary.PropositionalEquality.Core as P
import Relation.Binary.PropositionalEquality.Properties as P
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Function.Consequences

import Function.Construct.Identity as Identity
import Function.Construct.Symmetry as Symmetry
import Function.Construct.Composition as Composition

private
  variable
    a b ℓ ℓ₁ ℓ₂ : Level
    A B C D : Set a
    S T : Setoid a ℓ

------------------------------------------------------------------------
-- Setoid bundles

isEquivalence : IsEquivalence (Inverse {a} {b})
isEquivalence = record
  { refl  = λ {x} → Identity.inverse x
  ; sym   = Symmetry.inverse
  ; trans = Composition.inverse
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

open module ↔ {ℓ} = IsEquivalence (↔-isEquivalence {ℓ}) using ()
  renaming (refl to ↔-refl; sym to ↔-sym; trans to ↔-trans) public

------------------------------------------------------------------------
-- Conversion functions

Inverse⇒Injection : Inverse S T → Injection S T
Inverse⇒Injection {S = S} I = record
  { to = to
  ; cong = to-cong
  ; injective = inverseʳ⇒injective S {f⁻¹ = from} from-cong inverseʳ
  } where open Inverse I

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

↔⇒⤖ : A ↔ B → A ⤖ B
↔⇒⤖ = Inverse⇒Bijection

↔⇒⇔ : A ↔ B → A ⇔ B
↔⇒⇔ = Inverse⇒Equivalence

module _ (ext : ∀ {a b} → Extensionality a b) where

  ↔-fun : A ↔ B → C ↔ D → (A → C) ↔ (B → D)
  ↔-fun A↔B C↔D = mk↔′
    (λ a→c b → to C↔D (a→c (from A↔B b)))
    (λ b→d a → from C↔D (b→d (to A↔B a)))
    (λ b→d → ext λ _ → P.trans (inverseˡ C↔D _ ) (P.cong b→d (inverseˡ A↔B _)))
    (λ a→c → ext λ _ → P.trans (inverseʳ C↔D _ ) (P.cong a→c (inverseʳ A↔B _)))
    where open Inverse
