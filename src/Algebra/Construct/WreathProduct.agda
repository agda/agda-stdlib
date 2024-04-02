------------------------------------------------------------------------
-- The Agda standard library
--
-- Monoid Actions and Wreath Products of a Monoid with a Monoid Action
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Construct.WreathProduct where

open import Algebra.Bundles.Raw using (RawMonoid)
open import Algebra.Bundles using (Monoid)
open import Algebra.Structures using (IsMonoid)

open import Data.Product.Base using (_,_; _×_)

open import Function.Base using (flip)

open import Level using (Level; suc; _⊔_)

open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions

private
  variable
    a c r ℓ : Level


module MonoidAction (𝓜 : Monoid c ℓ) (𝓐 : Setoid a r) where

  private

    open module M = Monoid 𝓜 using () renaming (Carrier to M)
    open module A = Setoid 𝓐 using (_≈_) renaming (Carrier to A)

    variable
      x y z : A
      m n p q : M

  record RawMonoidAction : Set (a ⊔ r ⊔ c ⊔ ℓ)  where
    --constructor mkRawAct

    infixr 5 _∙_

    field
      _∙_ : M → A → A

  record MonoidAction (rawMonoidAction : RawMonoidAction) : Set (a ⊔ r ⊔ c ⊔ ℓ)  where
    --constructor mkAct

    open RawMonoidAction rawMonoidAction

    field
      ∙-cong : m M.≈ n → x ≈ y → m ∙ x ≈ n ∙ y
      ∙-act  : ∀ m n x → m M.∙ n ∙ x ≈ m ∙ n ∙ x
      ε-act  : ∀ x → M.ε ∙ x ≈ x

module LeftRegular (𝓜 : Monoid c ℓ) where
  private

    open module M = Monoid 𝓜 using (setoid)
    open MonoidAction 𝓜 setoid

  rawMonoidAction : RawMonoidAction
  rawMonoidAction = record { _∙_ = M._∙_ }

  monoidAction : MonoidAction rawMonoidAction
  monoidAction = record
    { ∙-cong = M.∙-cong
    ; ∙-act = M.assoc
    ; ε-act = M.identityˡ
    }

