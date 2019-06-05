------------------------------------------------------------------------
-- The Agda standard library
--
-- Packages for types of functions
------------------------------------------------------------------------

-- These definitions should usually be accessed from `Function`.

-- Note that these packages differ from those found elsewhere in other
-- library hierarchies as they take Setoids as parameters. This is
-- because a function is of no use without knowing what its domain and
-- codomain is, as well which equalities are being considered over them.
-- One consequence of this is that they are not built from the
-- definitions found in `Function.Structures` as is usually the case in
-- other library hierarchies, as this would duplicate the equality
-- axioms.

{-# OPTIONS --without-K --safe #-}

module Function.Packages where

import Function.Definitions as FunctionDefinitions
import Function.Structures as FunctionStructures
open import Level using (Level; _⊔_; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using () renaming (setoid to ≡-setoid)
open Setoid using (isEquivalence)

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Setoid packages

module _ (From : Setoid a ℓ₁) (To : Setoid b ℓ₂) where

  open Setoid From using () renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid To   using () renaming (Carrier to B; _≈_ to _≈₂_)
  open FunctionDefinitions _≈₁_ _≈₂_
  open FunctionStructures  _≈₁_ _≈₂_

  record Injection : Set (a ⊔ b ⊔ suc (ℓ₁ ⊔ ℓ₂)) where
    field
      f           : A → B
      cong        : f Preserves _≈₁_ ⟶ _≈₂_
      injective   : Injective f

    isInjection : IsInjection f
    isInjection = record
      { isPreserving = record
        { cong           = cong
        ; isEquivalence¹ = isEquivalence From
        ; isEquivalence² = isEquivalence To
        }
      ; injective    = injective
      }


  record Surjection : Set (a ⊔ b ⊔ suc (ℓ₁ ⊔ ℓ₂)) where
    field
      f          : A → B
      cong       : f Preserves _≈₁_ ⟶ _≈₂_
      surjective : Surjective f

    isSurjection : IsSurjection f
    isSurjection = record
      { isPreserving = record
        { cong           = cong
        ; isEquivalence¹ = isEquivalence From
        ; isEquivalence² = isEquivalence To
        }
      ; surjective   = surjective
      }


  record Bijection : Set (a ⊔ b ⊔ suc (ℓ₁ ⊔ ℓ₂)) where
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


  record Equivalence : Set (a ⊔ b ⊔ suc (ℓ₁ ⊔ ℓ₂)) where
    field
      f     : A → B
      g     : B → A
      cong¹ : f Preserves _≈₁_ ⟶ _≈₂_
      cong² : g Preserves _≈₂_ ⟶ _≈₁_


  record LeftInverse : Set (a ⊔ b ⊔ suc (ℓ₁ ⊔ ℓ₂)) where
    field
      f         : A → B
      g         : B → A
      cong¹     : f Preserves _≈₁_ ⟶ _≈₂_
      cong²     : g Preserves _≈₂_ ⟶ _≈₁_
      inverseˡ  : Inverseˡ f g

    isLeftInverse : IsLeftInverse f g
    isLeftInverse = record
      { isPreserving = record
        { cong           = cong¹
        ; isEquivalence¹ = isEquivalence From
        ; isEquivalence² = isEquivalence To
        }
      ; cong²        = cong²
      ; inverseˡ     = inverseˡ
      }

    equivalence : Equivalence
    equivalence = record
      { cong¹ = cong¹
      ; cong² = cong²
      }


  record RightInverse : Set (a ⊔ b ⊔ suc (ℓ₁ ⊔ ℓ₂)) where
    field
      f         : A → B
      g         : B → A
      cong¹     : f Preserves _≈₁_ ⟶ _≈₂_
      cong²     : g Preserves _≈₂_ ⟶ _≈₁_
      inverseʳ  : Inverseʳ f g

    isRightInverse : IsRightInverse f g
    isRightInverse = record
      { isPreserving = record
        { cong           = cong¹
        ; isEquivalence¹ = isEquivalence From
        ; isEquivalence² = isEquivalence To
        }
      ; cong²        = cong²
      ; inverseʳ     = inverseʳ
      }

    equivalence : Equivalence
    equivalence = record
      { cong¹ = cong¹
      ; cong² = cong²
      }


  record Inverse : Set (a ⊔ b ⊔ suc (ℓ₁ ⊔ ℓ₂)) where
    field
      f         : A → B
      f⁻¹       : B → A
      cong¹     : f Preserves _≈₁_ ⟶ _≈₂_
      cong²     : f⁻¹ Preserves _≈₂_ ⟶ _≈₁_
      inverse   : Inverseᵇ f f⁻¹

    inverseˡ : Inverseˡ f f⁻¹
    inverseˡ = proj₁ inverse

    inverseʳ : Inverseʳ f f⁻¹
    inverseʳ = proj₂ inverse

    leftInverse : LeftInverse
    leftInverse = record
      { cong¹    = cong¹
      ; cong²    = cong²
      ; inverseˡ = inverseˡ
      }

    rightInverse : RightInverse
    rightInverse = record
      { cong¹    = cong¹
      ; cong²    = cong²
      ; inverseʳ = inverseʳ
      }

    open LeftInverse leftInverse   public using (isLeftInverse)
    open RightInverse rightInverse public using (isRightInverse)

    isInverse : IsInverse f f⁻¹
    isInverse = record
      { isLeftInverse = isLeftInverse
      ; inverseʳ      = inverseʳ
      }

------------------------------------------------------------------------
-- Packages specialised for propositional equality

infix 3 _↣_ _↠_ _⤖_ _⇔_ _↞_ _↔_

_↣_ : Set a → Set b → Set _
From ↣ To = Injection (≡-setoid From) (≡-setoid To)

_↠_ : Set a → Set b → Set _
From ↠ To = Surjection (≡-setoid From) (≡-setoid To)

_⤖_ : Set a → Set b → Set _
From ⤖ To = Bijection (≡-setoid From) (≡-setoid To)

_⇔_ : Set a → Set b → Set _
From ⇔ To = Equivalence (≡-setoid From) (≡-setoid To)

_↞_ : Set a → Set b → Set _
From ↞ To = LeftInverse (≡-setoid From) (≡-setoid To)

_↔_ : Set a → Set b → Set _
From ↔ To = Inverse (≡-setoid From) (≡-setoid To)
