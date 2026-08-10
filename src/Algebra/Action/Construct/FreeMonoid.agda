------------------------------------------------------------------------
-- The Agda standard library
--
-- The free MonoidAction on a SetoidAction, arising from ListAction
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Algebra.Action.Construct.FreeMonoid
  {a c r ℓ} (S : Setoid c ℓ) (A : Setoid a r)
  where

open import Algebra.Action.Bundles
open import Algebra.Action.Structures using (IsLeftAction; IsRightAction)
open import Algebra.Bundles using (Monoid)

open import Data.List.Relation.Binary.Equality.Setoid.Properties S using (monoid)


------------------------------------------------------------------------
-- A Setoid action yields an iterated ListS action, which is
-- the underlying SetoidAction of the FreeMonoid construction

module SetoidActions where

  open SetoidAction
  open Monoid monoid using (setoid)

  leftAction : (left : Left S A) → Left setoid A
  leftAction left = record
    { isLeftAction = record
      { _▷_ = _▷⋆_
      ; ▷-cong = ▷⋆-cong
      }
    }
    where open Left left

  rightAction : (right : Right S A) → Right setoid A
  rightAction right = record
    { isRightAction = record
      { _◁_ = _◁⋆_
      ; ◁-cong = ◁⋆-cong
      }
    }
    where open Right right


------------------------------------------------------------------------
-- Now: define the MonoidActions of the (Monoid based on) ListS on A

module MonoidActions where

  open MonoidAction monoid A

  leftAction : (left : SetoidAction.Left S A) → Left (SetoidActions.leftAction left)
  leftAction left = record
    { ∙-act = ++-act
    ; ε-act = []-act
    }
    where open SetoidAction.Left left

  rightAction : (right : SetoidAction.Right S A) → Right (SetoidActions.rightAction right)
  rightAction right = record
    { ∙-act = ++-act
    ; ε-act = []-act
    }
    where open SetoidAction.Right right

