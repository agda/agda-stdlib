------------------------------------------------------------------------
-- The Agda standard library
--
-- Left- and right- regular actions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Action.Construct.Self where

open import Algebra.Action.Bundles
open import Algebra.Action.Structures using (IsLeftAction; IsRightAction)
open import Algebra.Bundles using (Monoid)

open import Data.Product.Base using (uncurry)

------------------------------------------------------------------------
-- Action of a Monoid over itself

module Regular {c ℓ} (M : Monoid c ℓ) where

  open Monoid M
  open MonoidAction M setoid

  private
    leftSetoidAction : SetoidAction.Left setoid setoid
    leftSetoidAction = record
      { act = record
        { to = uncurry _∙_
        ; cong = uncurry ∙-cong
        }
      }

    rightSetoidAction : SetoidAction.Right setoid setoid
    rightSetoidAction = record
      { act = record
        { to = uncurry _∙_
        ; cong = uncurry ∙-cong
        }
      }

  isLeftAction : IsLeftAction _≈_ _≈_
  isLeftAction = record { _ᴹ∙ᴬ_ = _∙_ ; ∙-cong = ∙-cong }

  isRightAction : IsRightAction _≈_ _≈_
  isRightAction = record { _ᴬ∙ᴹ_ = _∙_ ; ∙-cong = ∙-cong }

  leftAction : Left leftSetoidAction
  leftAction = record
    { ∙-act = assoc
    ; ε-act = identityˡ
    }

  rightAction : Right rightSetoidAction
  rightAction = record
    { ∙-act = λ x m n → sym (assoc x m n)
    ; ε-act = identityʳ
    }

