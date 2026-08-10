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

------------------------------------------------------------------------
-- Left- and Right- Actions of a Monoid over itself

module Regular {c ℓ} (M : Monoid c ℓ) where

  open Monoid M
  open MonoidAction M setoid

  isLeftAction : IsLeftAction _≈_ _≈_
  isLeftAction = record { _▷_ = _∙_ ; ▷-cong = ∙-cong }

  isRightAction : IsRightAction _≈_ _≈_
  isRightAction = record { _◁_ = _∙_ ; ◁-cong = ∙-cong }

  leftAction : Left record { isLeftAction = isLeftAction }
  leftAction = record
    { ∙-act = assoc
    ; ε-act = identityˡ
    }

  rightAction : Right record { isRightAction = isRightAction }
  rightAction = record
    { ∙-act = λ x m n → sym (assoc x m n)
    ; ε-act = identityʳ
    }

