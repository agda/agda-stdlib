------------------------------------------------------------------------
-- The Agda standard library
--
-- Setoid Actions and Monoid Actions
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Currently, this module (attempts to) systematically distinguish
-- between left- and right- actions, but unfortunately, trying to avoid
-- long names such as `Algebra.Action.Bundles.MonoidAction.LeftAction`
-- leads to the possibly/probably suboptimal use of `Left` and `Right` as
-- submodule names, when these are intended only to be used qualified by
-- the type of Action to which they refer, eg. as MonoidAction.Left etc.
------------------------------------------------------------------------


{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Action.Bundles where

open import Algebra.Action.Structures using (IsLeftAction; IsRightAction)
open import Algebra.Bundles using (Monoid)

open import Data.List.Base using ([]; _++_)
import Data.List.Relation.Binary.Equality.Setoid as ≋
open import Level using (Level; _⊔_)

open import Relation.Binary.Bundles using (Setoid)

private
  variable
    a c r ℓ : Level


------------------------------------------------------------------------
-- Basic definition: a Setoid action yields underlying raw action

module SetoidAction (M : Setoid c ℓ) (A : Setoid a r) where

  private

    module M = Setoid M
    module A = Setoid A

  record Left : Set (a ⊔ r ⊔ c ⊔ ℓ) where

    field
      isLeftAction : IsLeftAction M._≈_ A._≈_

  record Right : Set (a ⊔ r ⊔ c ⊔ ℓ) where

    field
      isRightAction : IsRightAction M._≈_ A._≈_


------------------------------------------------------------------------
-- A Setoid action yields an iterated List action

module ListAction {M : Setoid c ℓ} {A : Setoid a r} where

  open SetoidAction

  open ≋ M using (≋-setoid)

  leftAction : (left : Left M A) → Left ≋-setoid A
  leftAction left = record
    { isLeftAction = record
      { _▷_ = _▷⋆_
      ; ▷-cong = ▷⋆-cong
      }
    }
    where open Left left; open IsLeftAction isLeftAction

  rightAction : (right : Right M A) → Right ≋-setoid A
  rightAction right = record
    { isRightAction = record
      { _◁_ = _◁⋆_
      ; ◁-cong = ◁⋆-cong
      }
    }
    where open Right right; open IsRightAction isRightAction


------------------------------------------------------------------------
-- Definition: indexed over an underlying SetoidAction

module MonoidAction (M : Monoid c ℓ) (A : Setoid a r) where

  private

    open module M = Monoid M using (ε; _∙_; setoid)
    open module A = Setoid A using (_≈_)
    open ≋ setoid using (≋-refl)

  record Left (leftAction : SetoidAction.Left setoid A) : Set (a ⊔ r ⊔ c ⊔ ℓ)
    where

    open SetoidAction.Left leftAction public
      using (isLeftAction)
    open IsLeftAction isLeftAction public

    field
      ▷-act  : ∀ m n x → m ∙ n ▷ x ≈ m ▷ n ▷ x
      ε-act  : ∀ x → ε ▷ x ≈ x

    ▷-congˡ : ∀ {m x y} → x ≈ y → m ▷ x ≈ m ▷ y
    ▷-congˡ x≈y = ▷-cong M.refl x≈y

    ▷-congʳ : ∀ {m n x} → m M.≈ n → m ▷ x ≈ n ▷ x
    ▷-congʳ m≈n = ▷-cong m≈n A.refl

    ▷⋆-act : ∀ ms ns x → (ms ++ ns) ▷⋆ x ≈ ms ▷⋆ ns ▷⋆ x
    ▷⋆-act ms ns x = ▷⋆-act-cong ms ≋-refl A.refl

    []-act : ∀ x → [] ▷⋆ x ≈ x
    []-act _ = []-act-cong A.refl

  record Right (rightAction : SetoidAction.Right setoid A) : Set (a ⊔ r ⊔ c ⊔ ℓ)
    where

    open SetoidAction.Right rightAction public
      using (isRightAction)
    open IsRightAction isRightAction public

    field
      ◁-act  : ∀ x m n → x ◁ m ∙ n ≈ x ◁ m ◁ n
      ε-act  : ∀ x → x ◁ ε ≈ x

    ◁-congˡ : ∀ {x y m} → x ≈ y → x ◁ m ≈ y ◁ m
    ◁-congˡ x≈y = ◁-cong x≈y M.refl

    ◁-congʳ : ∀ {m n x} → m M.≈ n → x ◁ m ≈ x ◁ n
    ◁-congʳ m≈n = ◁-cong A.refl m≈n

    ◁⋆-act : ∀ x ms ns → x ◁⋆ (ms ++ ns) ≈ x ◁⋆ ms ◁⋆ ns
    ◁⋆-act x ms ns = ◁⋆-act-cong A.refl ms ≋-refl

    []-act : ∀ x → x ◁⋆ [] ≈ x
    []-act x = []-act-cong A.refl

