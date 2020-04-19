------------------------------------------------------------------------
-- The Agda standard library
--
-- Sum combinators for setoid equality preserving functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Function.Setoid where

open import Data.Sum.Base
open import Data.Sum.Relation.Binary.Pointwise
open import Relation.Binary
open import Function.Equality as F using (_⟶_; _⟨$⟩_)
open import Function.Equivalence as Eq
  using (Equivalence; _⇔_; module Equivalence)
open import Function.Injection as Inj
  using (Injection; _↣_; module Injection)
open import Function.Inverse as Inv
  using (Inverse; _↔_; module Inverse)
open import Function.LeftInverse as LeftInv
  using (LeftInverse; _↞_; _LeftInverseOf_; module LeftInverse)
open import Function.Related
open import Function.Surjection as Surj
  using (Surjection; _↠_; module Surjection)

------------------------------------------------------------------------
-- Combinators for equality preserving functions

module _  {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂}
          {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
          {C : Setoid c₁ c₂} {D : Setoid d₁ d₂}
          where

  _⊎-⟶_ : (A ⟶ B) → (C ⟶ D) → (A ⊎ₛ C) ⟶ (B ⊎ₛ D)
  _⊎-⟶_ f g = record
    { _⟨$⟩_ = fg
    ; cong  = fg-cong
    }
    where
    open Setoid (A ⊎ₛ C) using () renaming (_≈_ to _≈AC_)
    open Setoid (B ⊎ₛ D) using () renaming (_≈_ to _≈BD_)

    fg = map (_⟨$⟩_ f) (_⟨$⟩_ g)

    fg-cong : _≈AC_ =[ fg ]⇒ _≈BD_
    fg-cong (inj₁ x∼₁y) = inj₁ (F.cong f x∼₁y)
    fg-cong (inj₂ x∼₂y) = inj₂ (F.cong g x∼₂y)

module _ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} where

  inj₁ₛ : A ⟶ (A ⊎ₛ B)
  inj₁ₛ = record { _⟨$⟩_ = inj₁ ; cong = inj₁ }

  inj₂ₛ : B ⟶ (A ⊎ₛ B)
  inj₂ₛ = record { _⟨$⟩_ = inj₂ ; cong = inj₂ }

  [_,_]ₛ : ∀ {c₁ c₂} {C : Setoid c₁ c₂} →
           (A ⟶ C) → (B ⟶ C) → (A ⊎ₛ B) ⟶ C
  [ f , g ]ₛ = record
    { _⟨$⟩_ = [ f ⟨$⟩_ , g ⟨$⟩_ ]
    ; cong = λ where
      (inj₁ x∼₁y) → F.cong f x∼₁y
      (inj₂ x∼₂y) → F.cong g x∼₂y
    }

module _ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} where

  swapₛ : (A ⊎ₛ B) ⟶ (B ⊎ₛ A)
  swapₛ = [ inj₂ₛ , inj₁ₛ ]ₛ

------------------------------------------------------------------------
-- Combinators for more complex function types

module _  {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂}
          {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
          {C : Setoid c₁ c₂} {D : Setoid d₁ d₂}
          where

  _⊎-equivalence_ : Equivalence A B → Equivalence C D →
                    Equivalence (A ⊎ₛ C) (B ⊎ₛ D)
  A⇔B ⊎-equivalence C⇔D = record
    { to   = to   A⇔B ⊎-⟶ to   C⇔D
    ; from = from A⇔B ⊎-⟶ from C⇔D
    } where open Equivalence

  _⊎-injection_ : Injection A B → Injection C D →
                  Injection (A ⊎ₛ C) (B ⊎ₛ D)
  _⊎-injection_ A↣B C↣D = record
    { to        = to A↣B ⊎-⟶ to C↣D
    ; injective = inj _ _
    }
    where
    open Injection
    open Setoid (A ⊎ₛ C) using () renaming (_≈_ to _≈AC_)
    open Setoid (B ⊎ₛ D) using () renaming (_≈_ to _≈BD_)

    inj : ∀ x y →
          (to A↣B ⊎-⟶ to C↣D) ⟨$⟩ x ≈BD (to A↣B ⊎-⟶ to C↣D) ⟨$⟩ y →
          x ≈AC y
    inj (inj₁ x) (inj₁ y) (inj₁ x∼₁y) = inj₁ (injective A↣B x∼₁y)
    inj (inj₂ x) (inj₂ y) (inj₂ x∼₂y) = inj₂ (injective C↣D x∼₂y)

  _⊎-left-inverse_ : LeftInverse A B → LeftInverse C D →
                     LeftInverse (A ⊎ₛ C) (B ⊎ₛ D)
  A↞B ⊎-left-inverse C↞D = record
    { to              = Equivalence.to   eq
    ; from            = Equivalence.from eq
    ; left-inverse-of = [ (λ x → inj₁ (left-inverse-of A↞B x))
                        , (λ x → inj₂ (left-inverse-of C↞D x)) ]
    }
    where
    open LeftInverse
    eq = LeftInverse.equivalence A↞B ⊎-equivalence
         LeftInverse.equivalence C↞D

module _ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂}
         {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
         {C : Setoid c₁ c₂} {D : Setoid d₁ d₂}
         where

  _⊎-surjection_ : Surjection A B → Surjection C D →
                   Surjection (A ⊎ₛ C) (B ⊎ₛ D)
  A↠B ⊎-surjection C↠D = record
    { to         = LeftInverse.from inv
    ; surjective = record
      { from             = LeftInverse.to inv
      ; right-inverse-of = LeftInverse.left-inverse-of inv
      }
    }
    where
    open Surjection
    inv = right-inverse A↠B ⊎-left-inverse right-inverse C↠D

  _⊎-inverse_ : Inverse A B → Inverse C D →
                Inverse (A ⊎ₛ C) (B ⊎ₛ D)
  A↔B ⊎-inverse C↔D = record
    { to         = Surjection.to   surj
    ; from       = Surjection.from surj
    ; inverse-of = record
      { left-inverse-of  = LeftInverse.left-inverse-of inv
      ; right-inverse-of = Surjection.right-inverse-of surj
      }
    }
    where
    open Inverse
    surj = Inverse.surjection   A↔B ⊎-surjection
           Inverse.surjection   C↔D
    inv  = Inverse.left-inverse A↔B ⊎-left-inverse
           Inverse.left-inverse C↔D
