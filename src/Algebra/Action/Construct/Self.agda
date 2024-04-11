------------------------------------------------------------------------
-- The Agda standard library
--
-- The left- and right- regular actions: of a Monoid over itself
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Monoid)

module Algebra.Action.Construct.Self {c ℓ} (M : Monoid c ℓ) where

open import Algebra.Action.Bundles
open import Algebra.Action.Structures.Raw using (IsRawLeftAction; IsRawRightAction)
open import Data.Product.Base using (uncurry)

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

isRawLeftAction : IsRawLeftAction _≈_ _≈_
isRawLeftAction = record { _ᴹ∙ᴬ_ = _∙_ ; ∙-cong = ∙-cong }

isRawRightAction : IsRawRightAction _≈_ _≈_
isRawRightAction = record { _ᴬ∙ᴹ_ = _∙_ ; ∙-cong = ∙-cong }

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

