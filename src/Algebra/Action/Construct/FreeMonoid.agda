------------------------------------------------------------------------
-- The Agda standard library
--
-- The free MonoidAction on a SetoidAction, arising from ListAction
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Algebra.Action.Construct.FreeMonoid
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
-- First: define the Monoid structure on List M.Carrier
-- NB should be defined somewhere under `Data.List`!?

private

  open ≋ M using (_≋_; ≋-refl; ≋-reflexive; ≋-isEquivalence; ++⁺)

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

open MonoidAction monoid S

module _ (left : SetoidAction.Left M S) where

  private listAction = ListAction.leftAction left

  open SetoidAction.Left left

  leftAction : Left listAction
  leftAction = record
    { ∙-act = ++-act
    ; ε-act = []-act
    }

module _ (right : SetoidAction.Right M S) where

  private listAction = ListAction.rightAction right

  open SetoidAction.Right right

  rightAction : Right listAction
  rightAction = record
    { ∙-act = ++-act
    ; ε-act = []-act
    }

