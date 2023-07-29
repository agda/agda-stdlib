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

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Bundles where

open import Function.Base using (_∘_)
import Function.Definitions as FunctionDefinitions
import Function.Structures as FunctionStructures
open import Level using (Level; _⊔_; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary hiding (_⇔_)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_)
import Relation.Binary.PropositionalEquality.Properties as ≡
open Setoid using (isEquivalence)

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Setoid bundles
------------------------------------------------------------------------

module _ (From : Setoid a ℓ₁) (To : Setoid b ℓ₂) where

  open Setoid From using () renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid To   using () renaming (Carrier to B; _≈_ to _≈₂_)
  open FunctionDefinitions _≈₁_ _≈₂_
  open FunctionStructures  _≈₁_ _≈₂_

------------------------------------------------------------------------
-- Bundles with one element

  -- Called `Func` rather than `Function` in order to avoid clashing
  -- with the top-level module.
  record Func : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to   : A → B
      cong : to Preserves _≈₁_ ⟶ _≈₂_

    isCongruent : IsCongruent to
    isCongruent = record
      { cong           = cong
      ; isEquivalence₁ = isEquivalence From
      ; isEquivalence₂ = isEquivalence To
      }

    open IsCongruent isCongruent public
      using (module Eq₁; module Eq₂)


  record Injection : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to          : A → B
      cong        : to Preserves _≈₁_ ⟶ _≈₂_
      injective   : Injective to

    function : Func
    function = record
      { to   = to
      ; cong = cong
      }

    open Func function public
      hiding (to; cong)

    isInjection : IsInjection to
    isInjection = record
      { isCongruent = isCongruent
      ; injective   = injective
      }


  record Surjection : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to         : A → B
      cong       : to Preserves _≈₁_ ⟶ _≈₂_
      surjective : Surjective to

    to⁻ : B → A
    to⁻ = proj₁ ∘ surjective

    isCongruent : IsCongruent to
    isCongruent = record
      { cong           = cong
      ; isEquivalence₁ = isEquivalence From
      ; isEquivalence₂ = isEquivalence To
      }

    open IsCongruent isCongruent public using (module Eq₁; module Eq₂)

    isSurjection : IsSurjection to
    isSurjection = record
      { isCongruent = isCongruent
      ; surjective  = surjective
      }


  record Bijection : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to        : A → B
      cong      : to Preserves _≈₁_ ⟶ _≈₂_
      bijective : Bijective to

    injective : Injective to
    injective = proj₁ bijective

    surjective : Surjective to
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
    open Surjection surjection public using (isSurjection; to⁻)

    isBijection : IsBijection to
    isBijection = record
      { isInjection = isInjection
      ; surjective  = surjective
      }

    open IsBijection isBijection public using (module Eq₁; module Eq₂)


------------------------------------------------------------------------
-- Bundles with two elements

  record Equivalence : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to        : A → B
      from      : B → A
      to-cong   : to Preserves _≈₁_ ⟶ _≈₂_
      from-cong : from Preserves _≈₂_ ⟶ _≈₁_


  record LeftInverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to        : A → B
      from      : B → A
      to-cong   : to Preserves _≈₁_ ⟶ _≈₂_
      from-cong : from Preserves _≈₂_ ⟶ _≈₁_
      inverseˡ  : Inverseˡ to from

    isCongruent : IsCongruent to
    isCongruent = record
      { cong           = to-cong
      ; isEquivalence₁ = isEquivalence From
      ; isEquivalence₂ = isEquivalence To
      }

    open IsCongruent isCongruent public using (module Eq₁; module Eq₂)

    isLeftInverse : IsLeftInverse to from
    isLeftInverse = record
      { isCongruent = isCongruent
      ; from-cong   = from-cong
      ; inverseˡ    = inverseˡ
      }

    equivalence : Equivalence
    equivalence = record
      { to-cong   = to-cong
      ; from-cong = from-cong
      }


  record RightInverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to        : A → B
      from      : B → A
      to-cong   : to Preserves _≈₁_ ⟶ _≈₂_
      from-cong : from Preserves _≈₂_ ⟶ _≈₁_
      inverseʳ  : Inverseʳ to from

    isCongruent : IsCongruent to
    isCongruent = record
      { cong           = to-cong
      ; isEquivalence₁ = isEquivalence From
      ; isEquivalence₂ = isEquivalence To
      }

    isRightInverse : IsRightInverse to from
    isRightInverse = record
      { isCongruent = isCongruent
      ; from-cong   = from-cong
      ; inverseʳ    = inverseʳ
      }

    equivalence : Equivalence
    equivalence = record
      { to-cong   = to-cong
      ; from-cong = from-cong
      }


  record Inverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to        : A → B
      from      : B → A
      to-cong   : to Preserves _≈₁_ ⟶ _≈₂_
      from-cong : from Preserves _≈₂_ ⟶ _≈₁_
      inverse   : Inverseᵇ to from

    inverseˡ : Inverseˡ to from
    inverseˡ = proj₁ inverse

    inverseʳ : Inverseʳ to from
    inverseʳ = proj₂ inverse

    leftInverse : LeftInverse
    leftInverse = record
      { to-cong   = to-cong
      ; from-cong = from-cong
      ; inverseˡ  = inverseˡ
      }

    rightInverse : RightInverse
    rightInverse = record
      { to-cong   = to-cong
      ; from-cong = from-cong
      ; inverseʳ  = inverseʳ
      }

    open LeftInverse leftInverse   public using (isLeftInverse)
    open RightInverse rightInverse public using (isRightInverse)

    isInverse : IsInverse to from
    isInverse = record
      { isLeftInverse = isLeftInverse
      ; inverseʳ      = inverseʳ
      }

    open IsInverse isInverse public using (module Eq₁; module Eq₂)


------------------------------------------------------------------------
-- Bundles with three elements

  record BiEquivalence : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to         : A → B
      from₁      : B → A
      from₂      : B → A
      to-cong    : to Preserves _≈₁_ ⟶ _≈₂_
      from₁-cong : from₁ Preserves _≈₂_ ⟶ _≈₁_
      from₂-cong : from₂ Preserves _≈₂_ ⟶ _≈₁_


  record BiInverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      to         : A → B
      from₁        : B → A
      from₂        : B → A
      to-cong     : to Preserves _≈₁_ ⟶ _≈₂_
      from₁-cong     : from₁ Preserves _≈₂_ ⟶ _≈₁_
      from₂-cong     : from₂ Preserves _≈₂_ ⟶ _≈₁_
      inverseˡ  : Inverseˡ to from₁
      inverseʳ  : Inverseʳ to from₂

    to-isCongruent : IsCongruent to
    to-isCongruent = record
      { cong           = to-cong
      ; isEquivalence₁ = isEquivalence From
      ; isEquivalence₂ = isEquivalence To
      }

    isBiInverse : IsBiInverse to from₁ from₂
    isBiInverse = record
      { to-isCongruent = to-isCongruent
      ; from₁-cong     = from₁-cong
      ; from₂-cong     = from₂-cong
      ; inverseˡ       = inverseˡ
      ; inverseʳ       = inverseʳ
      }

    biEquivalence : BiEquivalence
    biEquivalence = record
      { to-cong    = to-cong
      ; from₁-cong = from₁-cong
      ; from₂-cong = from₂-cong
      }


------------------------------------------------------------------------
-- Bundles specialised for propositional equality
------------------------------------------------------------------------

infix 3 _⟶_ _↣_ _↠_ _⤖_ _⇔_ _↩_ _↪_ _↩↪_ _↔_
_⟶_ : Set a → Set b → Set _
A ⟶ B = Func (≡.setoid A) (≡.setoid B)

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

  mk⟶ : (A → B) → A ⟶ B
  mk⟶ to = record
    { to        = to
    ; cong      = ≡.cong to
    }

  mk↣ : ∀ {to : A → B} → Injective to → A ↣ B
  mk↣ {to} inj = record
    { to         = to
    ; cong      = ≡.cong to
    ; injective = inj
    }

  mk↠ : ∀ {to : A → B} → Surjective to → A ↠ B
  mk↠ {to} surj = record
    { to         = to
    ; cong       = ≡.cong to
    ; surjective = surj
    }

  mk⤖ : ∀ {to : A → B} → Bijective to → A ⤖ B
  mk⤖ {to} bij = record
    { to        = to
    ; cong      = ≡.cong to
    ; bijective = bij
    }

  mk⇔ : ∀ (to : A → B) (from : B → A) → A ⇔ B
  mk⇔ to from = record
    { to        = to
    ; from      = from
    ; to-cong   = ≡.cong to
    ; from-cong = ≡.cong from
    }

  mk↩ : ∀ {to : A → B} {from : B → A} → Inverseˡ to from → A ↩ B
  mk↩ {to} {from} invˡ = record
    { to        = to
    ; from      = from
    ; to-cong   = ≡.cong to
    ; from-cong = ≡.cong from
    ; inverseˡ  = invˡ
    }

  mk↪ : ∀ {to : A → B} {from : B → A} → Inverseʳ to from → A ↪ B
  mk↪ {to} {from} invʳ = record
    { to        = to
    ; from      = from
    ; to-cong   = ≡.cong to
    ; from-cong = ≡.cong from
    ; inverseʳ  = invʳ
    }

  mk↩↪ : ∀ {to : A → B} {from₁ : B → A} {from₂ : B → A} →
         Inverseˡ to from₁ → Inverseʳ to from₂ → A ↩↪ B
  mk↩↪ {to} {from₁} {from₂} invˡ invʳ = record
    { to         = to
    ; from₁      = from₁
    ; from₂      = from₂
    ; to-cong    = ≡.cong to
    ; from₁-cong = ≡.cong from₁
    ; from₂-cong = ≡.cong from₂
    ; inverseˡ   = invˡ
    ; inverseʳ   = invʳ
    }

  mk↔ : ∀ {to : A → B} {from : B → A} → Inverseᵇ to from → A ↔ B
  mk↔ {to} {from} inv = record
    { to        = to
    ; from      = from
    ; to-cong   = ≡.cong to
    ; from-cong = ≡.cong from
    ; inverse   = inv
    }

  -- Sometimes the implicit arguments above cannot be inferred
  mk↔′ : ∀ (to : A → B) (from : B → A) → Inverseˡ to from → Inverseʳ to from → A ↔ B
  mk↔′ to from invˡ invʳ = mk↔ {to = to} {from = from} (invˡ , invʳ)
