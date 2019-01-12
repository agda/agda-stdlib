------------------------------------------------------------------------
-- The Agda standard library
--
-- The basic code for equational reasoning with a single relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Reasoning.Base.Single
  {a ℓ} {A : Set a} (_∼_ : Rel A ℓ)
  (refl : Reflexive _∼_) (trans : Transitive _∼_)
  where

open import Relation.Binary.PropositionalEquality as P using (_≡_)

infix  4 _IsRelatedTo_
infix  3 _∎
infixr 2 _∼⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
infix  1 begin_

-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

data _IsRelatedTo_ (x y : A) : Set ℓ where
  relTo : (x∼y : x ∼ y) → x IsRelatedTo y

begin_ : ∀ {x y} → x IsRelatedTo y → x ∼ y
begin relTo x∼y = x∼y

_∼⟨_⟩_ : ∀ x {y z} → x ∼ y → y IsRelatedTo z → x IsRelatedTo z
_ ∼⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)

_≡⟨_⟩_ : ∀ x {y z} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
_ ≡⟨ P.refl ⟩ x∼z = x∼z

_≡⟨⟩_ : ∀ x {y} → x IsRelatedTo y → x IsRelatedTo y
_ ≡⟨⟩ x∼y = _ ≡⟨ P.refl ⟩ x∼y

_∎ : ∀ x → x IsRelatedTo x
_∎ _ = relTo refl

{-
private
  module Examples where
    postulate
      v w y d : A
      v≡w : v ≡ w
      w∼y : w ∼ y
      y≡d : y ≡ d

    u∼y : v ∼ d
    u∼y = begin
      v ≡⟨ v≡w ⟩
      w ∼⟨ w∼y ⟩
      y ≡⟨ y≡d ⟩
      d ∎
-}
