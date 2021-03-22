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

-- TODO: the following part is copied from Relation.Binary.Reasoning.Base.Partial
-- in order to avoid larger refactors. We will refactor this part later
-- so taht we use the same framework as Relation.Binary.Reasoning.Base.Partial.

open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality.Core as P
  using (_≡_)

infix  4 _IsRelatedTo_

------------------------------------------------------------------------
-- Definition of "related to"

-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

data _IsRelatedTo_ (x y : A) : Set ℓ where
  relTo : (x∼y : x ∼ y) → x IsRelatedTo y

------------------------------------------------------------------------
-- Reasoning combinators

-- Note that the arguments to the `step`s are not provided in their
-- "natural" order and syntax declarations are later used to re-order
-- them. This is because the `step` ordering allows the type-checker to
-- better infer the middle argument `y` from the `_IsRelatedTo_`
-- argument (see issue 622).
--
-- This has two practical benefits. First it speeds up type-checking by
-- approximately a factor of 5. Secondly it allows the combinators to be
-- used with macros that use reflection, e.g. `Tactic.RingSolver`, where
-- they need to be able to extract `y` using reflection.

infix  1 begin_
infixr 2 step-∼ step-≡ step-≡˘
infixr 2 _≡⟨⟩_
infix  3 _∎

-- Beginning of a proof

begin_ : ∀ {x y} → x IsRelatedTo y → x ∼ y
begin relTo x∼y = x∼y

-- Standard step with the relation

step-∼ : ∀ x {y z} → y IsRelatedTo z → x ∼ y → x IsRelatedTo z
step-∼ _ (relTo y∼z) x∼y = relTo (trans x∼y y∼z)

-- Step with a non-trivial propositional equality

step-≡ : ∀ x {y z} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
step-≡ _ x∼z P.refl = x∼z

-- Step with a flipped non-trivial propositional equality

step-≡˘ : ∀ x {y z} → y IsRelatedTo z → y ≡ x → x IsRelatedTo z
step-≡˘ _ x∼z P.refl = x∼z

-- Step with a trivial propositional equality

_≡⟨⟩_ : ∀ x {y} → x IsRelatedTo y → x IsRelatedTo y
_ ≡⟨⟩ x∼y = x∼y

-- Termination

_∎ : ∀ x → x IsRelatedTo x
x ∎ = relTo refl

-- Syntax declarations

syntax step-∼  x y∼z x∼y = x ∼⟨  x∼y ⟩ y∼z
syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z
