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
-- Basic definition: a Setoid action yields underlying action structure

module SetoidAction (S : Setoid c ℓ) (A : Setoid a r) where

  private

    module S = Setoid S
    module A = Setoid A

    open ≋ S using (≋-refl)

  record Left : Set (a ⊔ r ⊔ c ⊔ ℓ) where

    field
      isLeftAction : IsLeftAction S._≈_ A._≈_

    open IsLeftAction isLeftAction public

    ▷-congˡ : ∀ {m x y} → x A.≈ y → m ▷ x A.≈ m ▷ y
    ▷-congˡ x≈y = ▷-cong S.refl x≈y

    ▷-congʳ : ∀ {m n x} → m S.≈ n → m ▷ x A.≈ n ▷ x
    ▷-congʳ m≈n = ▷-cong m≈n A.refl

    []-act : ∀ x → [] ▷⋆ x A.≈ x
    []-act _ = []-act-cong A.refl

    ▷⋆-act : ∀ ms ns x → (ms ++ ns) ▷⋆ x A.≈ ms ▷⋆ ns ▷⋆ x
    ▷⋆-act ms ns x = ▷⋆-act-cong ms ≋-refl A.refl

  record Right : Set (a ⊔ r ⊔ c ⊔ ℓ) where

    field
      isRightAction : IsRightAction S._≈_ A._≈_

    open IsRightAction isRightAction public

    ◁-congˡ : ∀ {x y m} → x A.≈ y → x ◁ m A.≈ y ◁ m
    ◁-congˡ x≈y = ◁-cong x≈y S.refl

    ◁-congʳ : ∀ {m n x} → m S.≈ n → x ◁ m A.≈ x ◁ n
    ◁-congʳ m≈n = ◁-cong A.refl m≈n

    ◁⋆-act : ∀ x ms ns → x ◁⋆ (ms ++ ns) A.≈ x ◁⋆ ms ◁⋆ ns
    ◁⋆-act x ms ns = ◁⋆-act-cong A.refl ms ≋-refl

    []-act : ∀ x → x ◁⋆ [] A.≈ x
    []-act x = []-act-cong A.refl


------------------------------------------------------------------------
-- A Setoid action yields an iterated List action

module ListAction {S : Setoid c ℓ} {A : Setoid a r} where

  open SetoidAction

  open ≋ S using (≋-setoid)

  leftAction : (left : Left S A) → Left ≋-setoid A
  leftAction left = record
    { isLeftAction = record
      { _▷_ = _▷⋆_
      ; ▷-cong = ▷⋆-cong
      }
    }
    where open Left left

  rightAction : (right : Right S A) → Right ≋-setoid A
  rightAction right = record
    { isRightAction = record
      { _◁_ = _◁⋆_
      ; ◁-cong = ◁⋆-cong
      }
    }
    where open Right right


------------------------------------------------------------------------
-- Definition: indexed over an underlying SetoidAction

module MonoidAction (M : Monoid c ℓ) (A : Setoid a r) where

  private

    open module M = Monoid M using (ε; _∙_; setoid)
    open module A = Setoid A using (_≈_)

  record Left (leftAction : SetoidAction.Left setoid A) : Set (a ⊔ r ⊔ c ⊔ ℓ)
    where

    open SetoidAction.Left leftAction public

    field
      ▷-act  : ∀ m n x → m ∙ n ▷ x ≈ m ▷ n ▷ x
      ε-act  : ∀ x → ε ▷ x ≈ x

  record Right (rightAction : SetoidAction.Right setoid A) : Set (a ⊔ r ⊔ c ⊔ ℓ)
    where

    open SetoidAction.Right rightAction public

    field
      ◁-act  : ∀ x m n → x ◁ m ∙ n ≈ x ◁ m ◁ n
      ε-act  : ∀ x → x ◁ ε ≈ x
