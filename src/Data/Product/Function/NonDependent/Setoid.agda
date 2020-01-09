------------------------------------------------------------------------
-- The Agda standard library
--
-- Non-dependent product combinators for setoid equality preserving
-- functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Function.NonDependent.Setoid where

open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
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

  _×-⟶_ : (A ⟶ B) → (C ⟶ D) → (A ×ₛ C) ⟶ (B ×ₛ D)
  _×-⟶_ f g = record
    { _⟨$⟩_ = fg
    ; cong  = fg-cong
    }
    where
    open Setoid (A ×ₛ C) using () renaming (_≈_ to _≈AC_)
    open Setoid (B ×ₛ D) using () renaming (_≈_ to _≈BD_)

    fg = map (f ⟨$⟩_) (g ⟨$⟩_)

    fg-cong : _≈AC_ =[ fg ]⇒ _≈BD_
    fg-cong (_∼₁_ , _∼₂_) = (F.cong f _∼₁_ , F.cong g _∼₂_)

module _ {a₁ a₂ b₁ b₂ c₁ c₂}
         {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} {C : Setoid c₁ c₂}
         where

  <_,_>ₛ : (A ⟶ B) → (A ⟶ C) → A ⟶ (B ×ₛ C)
  < f , g >ₛ = record
    { _⟨$⟩_ = < f ⟨$⟩_ , g ⟨$⟩_ >
    ; cong = < F.cong f , F.cong g >
    }

module _ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} where

  proj₁ₛ : (A ×ₛ B) ⟶ A
  proj₁ₛ = record { _⟨$⟩_ = proj₁ ; cong = proj₁ }

  proj₂ₛ : (A ×ₛ B) ⟶ B
  proj₂ₛ = record { _⟨$⟩_ = proj₂ ; cong = proj₂ }

  swapₛ : (A ×ₛ B) ⟶ (B ×ₛ A)
  swapₛ = < proj₂ₛ , proj₁ₛ >ₛ

------------------------------------------------------------------------
-- Combinators for more complex function types

module _  {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂}
          {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
          {C : Setoid c₁ c₂} {D : Setoid d₁ d₂}
          where

  _×-equivalence_ : Equivalence A B → Equivalence C D →
                    Equivalence (A ×ₛ C) (B ×ₛ D)
  _×-equivalence_ A⇔B C⇔D = record
    { to   = to   A⇔B ×-⟶ to   C⇔D
    ; from = from A⇔B ×-⟶ from C⇔D
    } where open Equivalence

  _×-injection_ : Injection A B → Injection C D →
                  Injection (A ×ₛ C) (B ×ₛ D)
  A↣B ×-injection C↣D = record
    { to        = to A↣B ×-⟶ to C↣D
    ; injective = map (injective A↣B) (injective C↣D)
    } where open Injection

  _×-left-inverse_ : LeftInverse A B → LeftInverse C D →
                     LeftInverse (A ×ₛ C) (B ×ₛ D)
  A↞B ×-left-inverse C↞D = record
    { to              = Equivalence.to eq
    ; from            = Equivalence.from eq
    ; left-inverse-of = left
    }
    where
    open LeftInverse
    eq = LeftInverse.equivalence A↞B ×-equivalence
         LeftInverse.equivalence C↞D

    left : Equivalence.from eq LeftInverseOf Equivalence.to eq
    left (x , y) = (left-inverse-of A↞B x , left-inverse-of C↞D y)

module _ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂}
  {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
  {C : Setoid c₁ c₂} {D : Setoid d₁ d₂}
  where

  _×-surjection_ : Surjection A B → Surjection C D →
                   Surjection (A ×ₛ C) (B ×ₛ D)
  A↠B ×-surjection C↠D = record
    { to         = LeftInverse.from inv
    ; surjective = record
      { from             = LeftInverse.to inv
      ; right-inverse-of = LeftInverse.left-inverse-of inv
      }
    }
    where
    open Surjection
    inv = right-inverse A↠B ×-left-inverse right-inverse C↠D

  _×-inverse_ : Inverse A B → Inverse C D →
                Inverse (A ×ₛ C) (B ×ₛ D)
  A↔B ×-inverse C↔D = record
    { to         = Surjection.to   surj
    ; from       = Surjection.from surj
    ; inverse-of = record
      { left-inverse-of  = LeftInverse.left-inverse-of inv
      ; right-inverse-of = Surjection.right-inverse-of surj
      }
    }
    where
    open Inverse
    surj = Inverse.surjection   A↔B ×-surjection
           Inverse.surjection   C↔D
    inv  = Inverse.left-inverse A↔B ×-left-inverse
           Inverse.left-inverse C↔D
