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
infixr 2 step-∼ step-≡ step-≡˘
infixr 2 _≡⟨⟩_
infix  1 begin_

-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

data _IsRelatedTo_ (x y : A) : Set ℓ where
  relTo : (x∼y : x ∼ y) → x IsRelatedTo y

begin_ : ∀ {x y} → x IsRelatedTo y → x ∼ y
begin relTo x∼y = x∼y

step-∼ : ∀ x {y z} → y IsRelatedTo z → x ∼ y → x IsRelatedTo z
step-∼ _ (relTo y∼z) x∼y = relTo (trans x∼y y∼z)

syntax step-∼ x y∼z x∼y = x ∼⟨ x∼y ⟩ y∼z

step-≡ : ∀ x {y z} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
step-≡ _ x∼z P.refl = x∼z

syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

step-≡˘ : ∀ x {y z} → y IsRelatedTo z → y ≡ x → x IsRelatedTo z
step-≡˘ _ x∼z P.refl = x∼z

syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z

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
