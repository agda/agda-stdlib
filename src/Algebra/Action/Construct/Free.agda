------------------------------------------------------------------------
-- The Agda standard library
--
-- Monoid Actions and the free Monoid Action on a Setoid
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Algebra.Action.Construct.Free
  {a c r ℓ} (M : Setoid c ℓ) (S : Setoid a r)
  where

open import Algebra.Action.Bundles
open import Algebra.Action.Structures.Raw using (IsRawLeftAction; IsRawRightAction)
open import Algebra.Bundles using (Monoid)
open import Algebra.Structures using (IsMonoid)

open import Data.List.Base using (List; []; _++_)
import Data.List.Properties as List
import Data.List.Relation.Binary.Equality.Setoid as ≋
open import Data.Product.Base using (_,_)

open import Function.Base using (_∘_)

open import Level using (Level; _⊔_)


------------------------------------------------------------------------
-- Distinguished *free* action: lifting a raw action to a List action

module Free where

  open ≋ M using (_≋_; ≋-refl; ≋-reflexive; ≋-isEquivalence; ++⁺)
  open MonoidAction

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
      ; identity = (λ _ → ≋-refl) , ≋-reflexive ∘ List.++-identityʳ }

    monoid : Monoid c (c ⊔ ℓ)
    monoid = record { isMonoid = isMonoid }


  leftAction : (leftAction : SetoidAction.Left M S) →
               Left monoid S {!leftAction!}
  leftAction leftAction = record
    { ∙-act = λ ms ns x → ⋆-act-cong ms ≋-refl A.refl
    ; ε-act = λ _ → []-act-cong A.refl
    }
    where open SetoidAction.Left leftAction; open IsRawLeftAction isRawLeftAction

  rightAction : (rightAction : SetoidAction.Right M S) →
                Right monoid S {!rightAction!}
  rightAction rightAction = record
    { ∙-act = λ x ms ns → ⋆-act-cong A.refl ms ≋-refl
    ; ε-act = λ _ → []-act-cong A.refl
    }
    where open SetoidAction.Right rightAction; open IsRawRightAction isRawRightAction
