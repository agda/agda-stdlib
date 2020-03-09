------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundles for types of functions
------------------------------------------------------------------------

-- The contents of this file should usually be accessed from `Function`.

-- Note that these bundles differ from those found elsewhere in other
-- library hierarchies as they take Setoids as parameters. This is
-- because a function is of no use without knowing what its domain and
-- codomain is, as well which equalities are being considered over them.
-- One consequence of this is that they are not built from the
-- definitions found in `Function.Structures` as is usually the case in
-- other library hierarchies, as this would duplicate the equality
-- axioms.

{-# OPTIONS --without-K --safe #-}

module Function.Bundles where

import Function.Definitions as FunctionDefinitions
import Function.Structures as FunctionStructures
open import Level using (Level; _⊔_; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_)
open Setoid using (isEquivalence)

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Setoid bundles

module _ (From : Setoid a ℓ₁) (To : Setoid b ℓ₂) where

  open Setoid From using () renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid To   using () renaming (Carrier to B; _≈_ to _≈₂_)
  open FunctionDefinitions _≈₁_ _≈₂_
  open FunctionStructures  _≈₁_ _≈₂_

  record Injection : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      f           : A → B
      cong        : f Preserves _≈₁_ ⟶ _≈₂_
      injective   : Injective f

    isCongruent : IsCongruent f
    isCongruent = record
      { cong           = cong
      ; isEquivalence₁ = isEquivalence From
      ; isEquivalence₂ = isEquivalence To
      }

    open IsCongruent isCongruent public using (module Eq₁; module Eq₂)

    isInjection : IsInjection f
    isInjection = record
      { isCongruent = isCongruent
      ; injective   = injective
      }

  record Surjection : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      f          : A → B
      cong       : f Preserves _≈₁_ ⟶ _≈₂_
      surjective : Surjective f

    isCongruent : IsCongruent f
    isCongruent = record
      { cong           = cong
      ; isEquivalence₁ = isEquivalence From
      ; isEquivalence₂ = isEquivalence To
      }

    open IsCongruent isCongruent public using (module Eq₁; module Eq₂)

    isSurjection : IsSurjection f
    isSurjection = record
      { isCongruent = isCongruent
      ; surjective  = surjective
      }


  record Bijection : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      f         : A → B
      cong      : f Preserves _≈₁_ ⟶ _≈₂_
      bijective : Bijective f

    injective : Injective f
    injective = proj₁ bijective

    surjective : Surjective f
    surjective = proj₂ bijective

    injection : Injection
    injection = record
      { cong      = cong
      ; injective = injective
      }

    surjection : Surjection
    surjection = record
      { cong       = cong
      ; surjective = surjective
      }

    open Injection  injection  public using (isInjection)
    open Surjection surjection public using (isSurjection)

    isBijection : IsBijection f
    isBijection = record
      { isInjection = isInjection
      ; surjective  = surjective
      }

    open IsBijection isBijection public using (module Eq₁; module Eq₂)


  record Equivalence : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      f     : A → B
      g     : B → A
      cong₁ : f Preserves _≈₁_ ⟶ _≈₂_
      cong₂ : g Preserves _≈₂_ ⟶ _≈₁_


  record LeftInverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      f         : A → B
      g         : B → A
      cong₁     : f Preserves _≈₁_ ⟶ _≈₂_
      cong₂     : g Preserves _≈₂_ ⟶ _≈₁_
      inverseˡ  : Inverseˡ f g

    isCongruent : IsCongruent f
    isCongruent = record
      { cong           = cong₁
      ; isEquivalence₁ = isEquivalence From
      ; isEquivalence₂ = isEquivalence To
      }

    open IsCongruent isCongruent public using (module Eq₁; module Eq₂)

    isLeftInverse : IsLeftInverse f g
    isLeftInverse = record
      { isCongruent = isCongruent
      ; cong₂       = cong₂
      ; inverseˡ    = inverseˡ
      }

    equivalence : Equivalence
    equivalence = record
      { cong₁ = cong₁
      ; cong₂ = cong₂
      }


  record RightInverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      f         : A → B
      g         : B → A
      cong₁     : f Preserves _≈₁_ ⟶ _≈₂_
      cong₂     : g Preserves _≈₂_ ⟶ _≈₁_
      inverseʳ  : Inverseʳ f g

    isCongruent : IsCongruent f
    isCongruent = record
      { cong           = cong₁
      ; isEquivalence₁ = isEquivalence From
      ; isEquivalence₂ = isEquivalence To
      }

    isRightInverse : IsRightInverse f g
    isRightInverse = record
      { isCongruent = isCongruent
      ; cong₂       = cong₂
      ; inverseʳ    = inverseʳ
      }

    equivalence : Equivalence
    equivalence = record
      { cong₁ = cong₁
      ; cong₂ = cong₂
      }


  record BiEquivalence : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      f     : A → B
      g₁    : B → A
      g₂    : B → A
      cong₁ : f Preserves _≈₁_ ⟶ _≈₂_
      cong₂ : g₁ Preserves _≈₂_ ⟶ _≈₁_
      cong₃ : g₂ Preserves _≈₂_ ⟶ _≈₁_


  record BiInverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      f         : A → B
      g₁        : B → A
      g₂        : B → A
      cong₁     : f Preserves _≈₁_ ⟶ _≈₂_
      cong₂     : g₁ Preserves _≈₂_ ⟶ _≈₁_
      cong₃     : g₂ Preserves _≈₂_ ⟶ _≈₁_
      inverseˡ  : Inverseˡ f g₁
      inverseʳ  : Inverseʳ f g₂

    f-isCongruent : IsCongruent f
    f-isCongruent = record
      { cong           = cong₁
      ; isEquivalence₁ = isEquivalence From
      ; isEquivalence₂ = isEquivalence To
      }

    isBiInverse : IsBiInverse f g₁ g₂
    isBiInverse = record
      { f-isCongruent = f-isCongruent
      ; cong₂         = cong₂
      ; inverseˡ      = inverseˡ
      ; cong₃         = cong₃
      ; inverseʳ      = inverseʳ
      }

    biEquivalence : BiEquivalence
    biEquivalence = record
      { cong₁ = cong₁
      ; cong₂ = cong₂
      ; cong₃ = cong₃
      }


  record Inverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      f         : A → B
      f⁻¹       : B → A
      cong₁     : f Preserves _≈₁_ ⟶ _≈₂_
      cong₂     : f⁻¹ Preserves _≈₂_ ⟶ _≈₁_
      inverse   : Inverseᵇ f f⁻¹

    inverseˡ : Inverseˡ f f⁻¹
    inverseˡ = proj₁ inverse

    inverseʳ : Inverseʳ f f⁻¹
    inverseʳ = proj₂ inverse

    leftInverse : LeftInverse
    leftInverse = record
      { cong₁    = cong₁
      ; cong₂    = cong₂
      ; inverseˡ = inverseˡ
      }

    rightInverse : RightInverse
    rightInverse = record
      { cong₁    = cong₁
      ; cong₂    = cong₂
      ; inverseʳ = inverseʳ
      }

    open LeftInverse leftInverse   public using (isLeftInverse)
    open RightInverse rightInverse public using (isRightInverse)

    isInverse : IsInverse f f⁻¹
    isInverse = record
      { isLeftInverse = isLeftInverse
      ; inverseʳ      = inverseʳ
      }

    open IsInverse isInverse public using (module Eq₁; module Eq₂)

------------------------------------------------------------------------
-- Bundles specialised for propositional equality

infix 3 _↣_ _↠_ _⤖_ _⇔_ _↩_ _↪_ _↩↪_ _↔_

_↣_ : Set a → Set b → Set _
A ↣ B = Injection (≡.setoid A) (≡.setoid B)

_↠_ : Set a → Set b → Set _
A ↠ B = Surjection (≡.setoid A) (≡.setoid B)

_⤖_ : Set a → Set b → Set _
A ⤖ B = Bijection (≡.setoid A) (≡.setoid B)

_⇔_ : Set a → Set b → Set _
A ⇔ B = Equivalence (≡.setoid A) (≡.setoid B)

_↩_ : Set a → Set b → Set _
A ↩ B = LeftInverse (≡.setoid A) (≡.setoid B)

_↪_ : Set a → Set b → Set _
A ↪ B = RightInverse (≡.setoid A) (≡.setoid B)

_↩↪_ : Set a → Set b → Set _
A ↩↪ B = BiInverse (≡.setoid A) (≡.setoid B)

_↔_ : Set a → Set b → Set _
A ↔ B = Inverse (≡.setoid A) (≡.setoid B)

-- We now define some constructors for the above that
-- automatically provide the required congruency proofs.

module _ {A : Set a} {B : Set b} where

  open FunctionDefinitions {A = A} {B} _≡_ _≡_

  mk↣ : ∀ {f : A → B} → Injective f → A ↣ B
  mk↣ {f} inj = record
    { f         = f
    ; cong      = ≡.cong f
    ; injective = inj
    }

  mk↠ : ∀ {f : A → B} → Surjective f → A ↠ B
  mk↠ {f} surj = record
    { f          = f
    ; cong       = ≡.cong f
    ; surjective = surj
    }

  mk⤖ : ∀ {f : A → B} → Bijective f → A ⤖ B
  mk⤖ {f} bij = record
    { f         = f
    ; cong      = ≡.cong f
    ; bijective = bij
    }

  mk⇔ : ∀ (f : A → B) (g : B → A) → A ⇔ B
  mk⇔ f g = record
    { f     = f
    ; g     = g
    ; cong₁ = ≡.cong f
    ; cong₂ = ≡.cong g
    }

  mk↩ : ∀ {f : A → B} {g : B → A} → Inverseˡ f g → A ↩ B
  mk↩ {f} {g} invˡ = record
    { f        = f
    ; g        = g
    ; cong₁    = ≡.cong f
    ; cong₂    = ≡.cong g
    ; inverseˡ = invˡ
    }

  mk↪ : ∀ {f : A → B} {g : B → A} → Inverseʳ f g → A ↪ B
  mk↪ {f} {g} invʳ = record
    { f        = f
    ; g        = g
    ; cong₁    = ≡.cong f
    ; cong₂    = ≡.cong g
    ; inverseʳ = invʳ
    }

  mk↩↪ : ∀ {f : A → B} {g₁ : B → A} {g₂ : B → A}
    → Inverseˡ f g₁ → Inverseʳ f g₂ → A ↩↪ B
  mk↩↪ {f} {g₁} {g₂} invˡ invʳ = record
    { f        = f
    ; g₁       = g₁
    ; g₂       = g₂
    ; cong₁    = ≡.cong f
    ; cong₂    = ≡.cong g₁
    ; cong₃    = ≡.cong g₂
    ; inverseˡ = invˡ
    ; inverseʳ = invʳ
    }

  mk↔ : ∀ {f : A → B} {f⁻¹ : B → A} → Inverseᵇ f f⁻¹ → A ↔ B
  mk↔ {f} {f⁻¹} inv = record
    { f       = f
    ; f⁻¹     = f⁻¹
    ; cong₁   = ≡.cong f
    ; cong₂   = ≡.cong f⁻¹
    ; inverse = inv
    }
