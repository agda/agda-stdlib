------------------------------------------------------------------------
-- Convenient syntax for reasoning with a partial setoid
--
-- We can't re-use any of Relation.Binary.Reasoning.Base.Single because
-- it expects a reflexivity proof, which we obviously can't provide
------------------------------------------------------------------------
{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Reasoning.PartialSetoid {s₁ s₂} {A : Set s₁} (S : PartialSetoid A s₂) where

open import Level using (_⊔_)

open PartialSetoid S

infix  4 _IsRelatedTo_
infix  3 _∎⟨_⟩
infixr 2 _≈⟨_⟩_
infixr 2 _≈˘⟨_⟩_
infix  1 begin_

-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

data _IsRelatedTo_ (x y : A) : Set (s₁ ⊔ s₂) where
  relTo : (x≈y : x ≈ y) → x IsRelatedTo y

begin_ : ∀ {x y} → x IsRelatedTo y → x ≈ y
begin relTo x≈y = x≈y

_≈⟨_⟩_ : ∀ x {y z} → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
_ ≈⟨ x≈y ⟩ relTo y≈z = relTo (trans x≈y y≈z)

_≈˘⟨_⟩_ : ∀ x {y z} → y ≈ x → y IsRelatedTo z → x IsRelatedTo z
x ≈˘⟨ y≈x ⟩ y≈z = x ≈⟨ sym y≈x ⟩ y≈z

-- We need to explicitly show that x ≈ x
_∎⟨_⟩ : ∀ x → (x ≈ x) → x IsRelatedTo x
_∎⟨_⟩ x x≈x = relTo x≈x