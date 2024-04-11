------------------------------------------------------------------------
-- The Agda standard library
--
-- The left- and right- regular actions: of a Monoid over itself
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Monoid)

module Algebra.Action.Construct.Self {c ℓ} (M : Monoid c ℓ) where

open import Algebra.Action.Bundles using (module MonoidAction)
open import Algebra.Action.Structures.Raw using (IsRawLeftAction; IsRawRightAction)

open Monoid M
open MonoidAction M setoid

private
  isRawLeftAction : IsRawLeftAction _≈_ _≈_
  isRawLeftAction = record { _ᴹ∙ᴬ_ = _∙_ ; ∙-cong = ∙-cong }

  isRawRightAction : IsRawRightAction _≈_ _≈_
  isRawRightAction = record { _ᴬ∙ᴹ_ = _∙_ ; ∙-cong = ∙-cong }

leftAction : Left {!isRawLeftAction!}
leftAction = record
  { ∙-act = assoc
  ; ε-act = identityˡ
  }

rightAction : Right {!isRawRightAction!}
rightAction = record
  { ∙-act = λ x m n → sym (assoc x m n)
  ; ε-act = identityʳ
  }

