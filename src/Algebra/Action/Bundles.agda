------------------------------------------------------------------------
-- The Agda standard library
--
-- Monoid Actions and the free Monoid Action on a Setoid
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Action.Bundles where

open import Algebra.Action.Structures.Raw using (IsRawLeftAction; IsRawRightAction)
open import Algebra.Bundles using (Monoid)

open import Data.List.Base using ([]; _++_)
import Data.List.Relation.Binary.Equality.Setoid as ≋
open import Data.Product.Base using (curry)
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

    isRawLeftAction : IsRawLeftAction M._≈_ _≈_
    isRawLeftAction = record { _ᴹ∙ᴬ_ = curry to ; ∙-cong = curry cong }
      where open Func act

  record Right : Set (a ⊔ r ⊔ c ⊔ ℓ) where

    field
      act : Func (A ×ₛ M) A

    isRawRightAction : IsRawRightAction M._≈_ _≈_
    isRawRightAction = record { _ᴬ∙ᴹ_ = curry to ; ∙-cong = curry cong }
      where open Func act


------------------------------------------------------------------------
-- Definition: indexed over an underlying raw action

module MonoidAction (M : Monoid c ℓ) (A : Setoid a r) where

  private

    open module M = Monoid M using ()
    open module A = Setoid A using (_≈_)
    open ≋ M.setoid using (≋-refl)

  record Left (isRawLeftAction : IsRawLeftAction M._≈_ _≈_) : Set (a ⊔ r ⊔ c ⊔ ℓ)
    where

    open IsRawLeftAction isRawLeftAction public
      renaming (_ᴹ∙ᴬ_ to _∙_; _ᴹ⋆ᴬ_ to _⋆_)

    field
      ∙-act  : ∀ m n x → m M.∙ n ∙ x ≈ m ∙ n ∙ x
      ε-act  : ∀ x → M.ε ∙ x ≈ x

    ∙-congˡ : ∀ {m x y} → x ≈ y → m ∙ x ≈ m ∙ y
    ∙-congˡ x≈y = ∙-cong M.refl x≈y

    ∙-congʳ : ∀ {m n x} → m M.≈ n → m ∙ x ≈ n ∙ x
    ∙-congʳ m≈n = ∙-cong m≈n A.refl

    ⋆-act : ∀ ms ns x → (ms ++ ns) ⋆ x ≈ ms ⋆ ns ⋆ x
    ⋆-act ms ns x = ⋆-act-cong ms ≋-refl A.refl

    []-act : ∀ x → [] ⋆ x ≈ x
    []-act _ = []-act-cong A.refl

  record Right (isRawRightAction : IsRawRightAction M._≈_ _≈_) : Set (a ⊔ r ⊔ c ⊔ ℓ)
    where

    open IsRawRightAction isRawRightAction public
      renaming (_ᴬ∙ᴹ_ to _∙_; _ᴬ⋆ᴹ_ to _⋆_)

    field
      ∙-act  : ∀ x m n → x ∙ m M.∙ n ≈ x ∙ m ∙ n
      ε-act  : ∀ x → x ∙ M.ε ≈ x

    ∙-congˡ : ∀ {x y m} → x ≈ y → x ∙ m ≈ y ∙ m
    ∙-congˡ x≈y = ∙-cong x≈y M.refl

    ∙-congʳ : ∀ {m n x} → m M.≈ n → x ∙ m ≈ x ∙ n
    ∙-congʳ m≈n = ∙-cong A.refl m≈n

    ⋆-act : ∀ x ms ns → x ⋆ (ms ++ ns) ≈ x ⋆ ms ⋆ ns
    ⋆-act x ms ns = ⋆-act-cong A.refl ms ≋-refl

    []-act : ∀ x → x ⋆ [] ≈ x
    []-act x = []-act-cong A.refl

