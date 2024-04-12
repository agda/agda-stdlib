------------------------------------------------------------------------
-- The Agda standard library
--
-- Setoid Actions and Monoid Actions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Action.Bundles where

open import Algebra.Action.Structures using (IsLeftAction; IsRightAction)
open import Algebra.Bundles using (Monoid)

open import Data.List.Base using ([]; _++_)
import Data.List.Relation.Binary.Equality.Setoid as ≋
open import Data.Product.Base using (curry; uncurry)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)

open import Function.Bundles using (Func)

open import Level using (Level; _⊔_)

open import Relation.Binary.Bundles using (Setoid)

private
  variable
    a c r ℓ : Level


------------------------------------------------------------------------
-- Basic definition: a Setoid action yields underlying raw action

module SetoidAction (M : Setoid c ℓ) (A : Setoid a r) where

  private

    open module M = Setoid M using ()
    open module A = Setoid A using (_≈_)

  record Left : Set (a ⊔ r ⊔ c ⊔ ℓ) where

    field
      act : Func (M ×ₛ A) A

    isLeftAction : IsLeftAction M._≈_ _≈_
    isLeftAction = record { _ᴹ∙ᴬ_ = curry to ; ∙-cong = curry cong }
      where open Func act

  record Right : Set (a ⊔ r ⊔ c ⊔ ℓ) where

    field
      act : Func (A ×ₛ M) A

    isRightAction : IsRightAction M._≈_ _≈_
    isRightAction = record { _ᴬ∙ᴹ_ = curry to ; ∙-cong = curry cong }
      where open Func act


------------------------------------------------------------------------
-- A Setoid action yields an iterated List action

module _ {M : Setoid c ℓ} {A : Setoid a r} where

  open SetoidAction

  open ≋ M using (≋-setoid)

  leftListAction : (leftAction : Left M A) → Left ≋-setoid A
  leftListAction leftAction = record
    { act = record
      { to = uncurry _ᴹ⋆ᴬ_ ; cong = uncurry ⋆-cong }
    }
    where open Left leftAction; open IsLeftAction isLeftAction

  rightListAction : (rightAction : Right M A) → Right ≋-setoid A
  rightListAction rightAction = record
    { act = record
      { to = uncurry _ᴬ⋆ᴹ_ ; cong = uncurry ⋆-cong }
    }
    where open Right rightAction; open IsRightAction isRightAction


------------------------------------------------------------------------
-- Definition: indexed over an underlying SetoidAction

module MonoidAction (M : Monoid c ℓ) (A : Setoid a r) where

  private

    open module M = Monoid M using (ε) renaming (_∙_ to _∙ᴹ_)
    open module A = Setoid A using (_≈_)
    open ≋ M.setoid using (≋-refl)

  record Left (leftAction : SetoidAction.Left M.setoid A) : Set (a ⊔ r ⊔ c ⊔ ℓ)
    where

    open SetoidAction.Left leftAction public
      using (isLeftAction)
    open IsLeftAction isLeftAction public
      renaming (_ᴹ∙ᴬ_ to _∙_; _ᴹ⋆ᴬ_ to _⋆_)

    field
      ∙-act  : ∀ m n x → m ∙ᴹ n ∙ x ≈ m ∙ n ∙ x
      ε-act  : ∀ x → ε ∙ x ≈ x

    ∙-congˡ : ∀ {m x y} → x ≈ y → m ∙ x ≈ m ∙ y
    ∙-congˡ x≈y = ∙-cong M.refl x≈y

    ∙-congʳ : ∀ {m n x} → m M.≈ n → m ∙ x ≈ n ∙ x
    ∙-congʳ m≈n = ∙-cong m≈n A.refl

    ⋆-act : ∀ ms ns x → (ms ++ ns) ⋆ x ≈ ms ⋆ ns ⋆ x
    ⋆-act ms ns x = ⋆-act-cong ms ≋-refl A.refl

    []-act : ∀ x → [] ⋆ x ≈ x
    []-act _ = []-act-cong A.refl

  record Right (rightAction : SetoidAction.Right M.setoid A) : Set (a ⊔ r ⊔ c ⊔ ℓ)
    where

    open SetoidAction.Right rightAction public
      using (isRightAction)
    open IsRightAction isRightAction public
      renaming (_ᴬ∙ᴹ_ to _∙_; _ᴬ⋆ᴹ_ to _⋆_)

    field
      ∙-act  : ∀ x m n → x ∙ m ∙ᴹ n ≈ x ∙ m ∙ n
      ε-act  : ∀ x → x ∙ ε ≈ x

    ∙-congˡ : ∀ {x y m} → x ≈ y → x ∙ m ≈ y ∙ m
    ∙-congˡ x≈y = ∙-cong x≈y M.refl

    ∙-congʳ : ∀ {m n x} → m M.≈ n → x ∙ m ≈ x ∙ n
    ∙-congʳ m≈n = ∙-cong A.refl m≈n

    ⋆-act : ∀ x ms ns → x ⋆ (ms ++ ns) ≈ x ⋆ ms ⋆ ns
    ⋆-act x ms ns = ⋆-act-cong A.refl ms ≋-refl

    []-act : ∀ x → x ⋆ [] ≈ x
    []-act x = []-act-cong A.refl

