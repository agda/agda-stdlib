------------------------------------------------------------------------
-- The Agda standard library
--
-- Packages for types of functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Packages where

open import Function.Definitions
open import Function.Structures
open import Level using (_⊔_; suc)
open import Relation.Binary using (Rel; Setoid)
open import Relation.Binary.PropositionalEquality using (setoid)
open Setoid using (Carrier; _≈_)

------------------------------------------------------------------------
-- Setoid packages

record Injection {a b ℓ₁ ℓ₂} (From : Setoid a ℓ₁) (To : Setoid b ℓ₂)
                 : Set (a ⊔ b ⊔ suc (ℓ₁ ⊔ ℓ₂)) where
  field
    f           : Carrier From → Carrier To
    isInjection : IsInjection (_≈_ From) (_≈_ To) f

  open IsInjection isInjection public


record Surjection {a b ℓ₁ ℓ₂} (From : Setoid a ℓ₁) (To : Setoid b ℓ₂)
                  : Set (a ⊔ b ⊔ suc (ℓ₁ ⊔ ℓ₂)) where
  field
    f            : Carrier From → Carrier To
    isSurjection : IsSurjection (_≈_ From) (_≈_ To)  f

  open IsSurjection isSurjection public


record Bijection {a b ℓ₁ ℓ₂} (From : Setoid a ℓ₁) (To : Setoid b ℓ₂)
                 : Set (a ⊔ b ⊔ suc (ℓ₁ ⊔ ℓ₂)) where
  field
    f           : Carrier From → Carrier To
    isBijection : IsBijection (_≈_ From) (_≈_ To)  f

  open IsBijection isBijection public

  injection : Injection From To
  injection = record
    { isInjection = isInjection
    }

  surjection : Surjection From To
  surjection = record
    { isSurjection = isSurjection
    }

record Equivalence {a b ℓ₁ ℓ₂} (From : Setoid a ℓ₁) (To : Setoid b ℓ₂) :
                   Set (a ⊔ b ⊔ suc (ℓ₁ ⊔ ℓ₂)) where
  field
    f     : Carrier From → Carrier To
    g     : Carrier To → Carrier From
    cong¹ : Congruent (_≈_ From) (_≈_ To) f
    cong² : Congruent (_≈_ To) (_≈_ From) g

record LeftInverse {a b ℓ₁ ℓ₂} (From : Setoid a ℓ₁) (To : Setoid b ℓ₂)
                   : Set (a ⊔ b ⊔ suc (ℓ₁ ⊔ ℓ₂)) where
  field
    f             : Carrier From → Carrier To
    g             : Carrier To → Carrier From
    isLeftInverse : IsLeftInverse (_≈_ From) (_≈_ To) f g

  open IsLeftInverse isLeftInverse public


record RightInverse {a b ℓ₁ ℓ₂} (From : Setoid a ℓ₁) (To : Setoid b ℓ₂)
                    : Set (a ⊔ b ⊔ suc (ℓ₁ ⊔ ℓ₂)) where
  field
    f             : Carrier From → Carrier To
    g             : Carrier To → Carrier From
    isRightInverse : IsRightInverse (_≈_ From) (_≈_ To) f g

  open IsRightInverse isRightInverse public


record Inverse {a b ℓ₁ ℓ₂} (From : Setoid a ℓ₁) (To : Setoid b ℓ₂)
               : Set (a ⊔ b ⊔ suc (ℓ₁ ⊔ ℓ₂)) where
  field
    f         : Carrier From → Carrier To
    g         : Carrier To → Carrier From
    isInverse : IsInverse (_≈_ From) (_≈_ To) f g

  open IsInverse isInverse public

  leftInverse : LeftInverse From To
  leftInverse = record
    { isLeftInverse = isLeftInverse
    }

  rightInverse : RightInverse From To
  rightInverse = record
    { isRightInverse = isRightInverse
    }

------------------------------------------------------------------------
-- Packages over propositional equality

infix 3 _↣_ _↠_ _⤖_ _⇔_ _↞_ _↔_

_↣_ : ∀ {f t} → Set f → Set t → Set _
From ↣ To = Injection (setoid From) (setoid To)

_↠_ : ∀ {f t} → Set f → Set t → Set _
From ↠ To = Surjection (setoid From) (setoid To)

_⤖_ : ∀ {f t} → Set f → Set t → Set _
From ⤖ To = Bijection (setoid From) (setoid To)

_⇔_ : ∀ {f t} → Set f → Set t → Set _
From ⇔ To = Equivalence (setoid From) (setoid To)

_↞_ : ∀ {f t} → Set f → Set t → Set _
From ↞ To = LeftInverse (setoid From) (setoid To)

_↔_ : ∀ {f t} → Set f → Set t → Set _
From ↔ To = Inverse (setoid From) (setoid To)
