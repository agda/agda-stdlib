------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of equivalences. This file is designed to be
-- imported qualified.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Properties.Equivalence where

open import Function.Bundles
open import Level
open import Relation.Binary.Definitions
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
import Relation.Binary.PropositionalEquality.Properties as ≡

import Function.Construct.Identity as Identity
import Function.Construct.Symmetry as Symmetry
import Function.Construct.Composition as Composition

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B : Set a
    S T : Setoid a ℓ

------------------------------------------------------------------------
-- Constructors

mkEquivalence : Func S T → Func T S → Equivalence S T
mkEquivalence f g = record
  { to = to f
  ; from = to g
  ; to-cong = cong f
  ; from-cong = cong g
  } where open Func

⟶×⟵⇒⇔ : A ⟶ B → B ⟶ A → A ⇔ B
⟶×⟵⇒⇔ = mkEquivalence

------------------------------------------------------------------------
-- Destructors

⇔⇒⟶ : A ⇔ B → A ⟶ B
⇔⇒⟶ = Equivalence.toFunction

⇔⇒⟵ : A ⇔ B → B ⟶ A
⇔⇒⟵ = Equivalence.fromFunction

------------------------------------------------------------------------
-- Setoid bundles

refl : Reflexive (Equivalence {a} {ℓ})
refl {x = x} = Identity.equivalence x

sym : Sym (Equivalence {a} {ℓ₁} {b} {ℓ₂})
          (Equivalence {b} {ℓ₂} {a} {ℓ₁})
sym = Symmetry.equivalence

trans : Trans (Equivalence {a} {ℓ₁} {b} {ℓ₂})
              (Equivalence {b} {ℓ₂} {c} {ℓ₃})
              (Equivalence {a} {ℓ₁} {c} {ℓ₃})
trans = Composition.equivalence

isEquivalence : IsEquivalence (Equivalence {a} {ℓ})
isEquivalence = record
  { refl = refl
  ; sym = sym
  ; trans = Composition.equivalence
  }

setoid : (s₁ s₂ : Level) → Setoid (suc (s₁ ⊔ s₂)) (s₁ ⊔ s₂)
setoid s₁ s₂ = record
  { Carrier       = Setoid s₁ s₂
  ; _≈_           = Equivalence
  ; isEquivalence = isEquivalence
  }

------------------------------------------------------------------------
-- Propositional bundles

⇔-isEquivalence : IsEquivalence {ℓ = ℓ} _⇔_
⇔-isEquivalence = record
  { refl = λ {x} → Identity.equivalence (≡.setoid x)
  ; sym = Symmetry.equivalence
  ; trans = Composition.equivalence
  }

⇔-setoid : (ℓ : Level) → Setoid (suc ℓ) ℓ
⇔-setoid ℓ = record
  { Carrier       = Set ℓ
  ; _≈_           = _⇔_
  ; isEquivalence = ⇔-isEquivalence
  }
