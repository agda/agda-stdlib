------------------------------------------------------------------------
-- The Agda standard library
--
-- The basic code for equational reasoning with a non-reflexive relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality.Core as P
  using (_≡_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True)

module Relation.Binary.Reasoning.Base.Partial
  {a ℓ} {A : Set a} (_∼_ : Rel A ℓ) (trans : Transitive _∼_)
  where

------------------------------------------------------------------------
-- Definition of "related to"

-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

infix  4 _IsRelatedTo_

data _IsRelatedTo_ : A → A → Set (a ⊔ ℓ) where
  singleStep : ∀ x → x IsRelatedTo x
  multiStep  : ∀ {x y} (x∼y : x ∼ y) → x IsRelatedTo y

------------------------------------------------------------------------
-- Types that are used to ensure that the final relation proved by the
-- chain of reasoning can be converted into the required relation.

data IsMultiStep {x y} : x IsRelatedTo y → Set (a ⊔ ℓ) where
  isMultiStep : ∀ x∼y → IsMultiStep (multiStep x∼y)

IsMultiStep? : ∀ {x y} (x∼y : x IsRelatedTo y) → Dec (IsMultiStep x∼y)
IsMultiStep? (multiStep x<y) = yes (isMultiStep x<y)
IsMultiStep? (singleStep _)  = no λ()

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
infix  3 _∎⟨_⟩ _∎

-- Beginning of a proof

begin_ : ∀ {x y} (x∼y : x IsRelatedTo y) → {True (IsMultiStep? x∼y)} → x ∼ y
begin (multiStep x∼y) = x∼y

-- Standard step with the relation

step-∼ : ∀ x {y z} → y IsRelatedTo z → x ∼ y → x IsRelatedTo z
step-∼ _ (singleStep _) x∼y  = multiStep x∼y
step-∼ _ (multiStep y∼z) x∼y = multiStep (trans x∼y y∼z)

-- Step with a non-trivial propositional equality

step-≡ : ∀ x {y z} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
step-≡ _ x∼z P.refl = x∼z

-- Step with a flipped non-trivial propositional equality

step-≡˘ : ∀ x {y z} → y IsRelatedTo z → y ≡ x → x IsRelatedTo z
step-≡˘ _ x∼z P.refl = x∼z

-- -- Step with a trivial propositional equality

_≡⟨⟩_ : ∀ x {y} → x IsRelatedTo y → x IsRelatedTo y
_ ≡⟨⟩ x∼y = x∼y

-- Termination

_∎ : ∀ x → x IsRelatedTo x
_∎ = singleStep

-- Syntax declarations

syntax step-∼  x y∼z x∼y = x ∼⟨  x∼y ⟩ y∼z
syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.6

_∎⟨_⟩ : ∀ x → x ∼ x → x IsRelatedTo x
_ ∎⟨ x∼x ⟩ = multiStep x∼x
{-# WARNING_ON_USAGE _∎⟨_⟩
"Warning: _∎⟨_⟩ was deprecated in v1.6.
Please use _∎ instead if used in a chain, otherwise simply provide
the proof of reflexivity directly without using these combinators."
#-}

