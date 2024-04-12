------------------------------------------------------------------------
-- The Agda standard library
--
-- The free MonoidAction on a SetoidAction
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Algebra.Action.Construct.Free
  {a c r ℓ} (M : Setoid c ℓ) (S : Setoid a r)
  where

open import Algebra.Action.Bundles
open import Algebra.Action.Structures using (IsLeftAction; IsRightAction)
open import Algebra.Bundles using (Monoid)
open import Algebra.Structures using (IsMonoid)

open import Data.List.Base using (List; []; _++_)
import Data.List.Properties as List
import Data.List.Relation.Binary.Equality.Setoid as ≋
open import Data.Product.Base using (_,_)

open import Function.Base using (_∘_)

open import Level using (Level; _⊔_)

------------------------------------------------------------------------
-- Monoid: the Free action arises from List

module FreeMonoidAction where

  open ≋ M using (_≋_; ≋-refl; ≋-reflexive; ≋-isEquivalence; ++⁺)
  open MonoidAction

------------------------------------------------------------------------
-- First: define the Monoid structure on List M.Carrier

  private

    module M = Setoid M
    module A = Setoid S

    isMonoid : IsMonoid _≋_ _++_ []
    isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = ≋-isEquivalence
          ; ∙-cong = ++⁺
          }
        ; assoc = λ xs ys zs → ≋-reflexive (List.++-assoc xs ys zs)
        }
      ; identity = (λ _ → ≋-refl) , ≋-reflexive ∘ List.++-identityʳ
      }

    monoid : Monoid c (c ⊔ ℓ)
    monoid = record { isMonoid = isMonoid }


------------------------------------------------------------------------
-- Second: define the actions of that Monoid

  module _ (left : SetoidAction.Left M S) where

    private listAction = leftListAction left

    open SetoidAction.Left left
    open IsLeftAction isLeftAction

    leftAction : Left monoid S listAction
    leftAction = record
      { ∙-act = λ ms ns x → ⋆-act-cong ms ≋-refl A.refl
      ; ε-act = λ _ → A.refl
      }

  module _ (right : SetoidAction.Right M S) where

    private listAction = rightListAction right

    open SetoidAction.Right right
    open IsRightAction isRightAction

    rightAction : Right monoid S listAction
    rightAction = record
      { ∙-act = λ x ms ns → ⋆-act-cong A.refl ms ≋-refl
      ; ε-act = λ _ → A.refl
      }

