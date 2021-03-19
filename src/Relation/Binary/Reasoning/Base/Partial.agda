------------------------------------------------------------------------
-- The Agda standard library
--
-- The basic code for equational reasoning with a partial relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Reasoning.Base.Partial
  {a ℓ} {A : Set a} (_∼_ : Rel A ℓ) (trans : Transitive _∼_)
  where

open import Level using (_⊔_; suc)
open import Relation.Binary.PropositionalEquality.Core as P
  using (_≡_)
infix  4 [_]_IsRelatedTo_
infix  3 _∎⟨_⟩ _∎
infixr 2 step-∼ step-≡ step-≡˘
infixr 2 _≡⟨⟩_
infix  1 begin_

------------------------------------------------------------------------
-- Definition of "related to"

-- this is a type which remember whether transitivity is used. check begin_ below

data Flag : Set where
  single : Flag
  multi  : Flag

-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

data [_]_IsRelatedTo_ : Flag → A → A → Set (a ⊔ ℓ) where
  emp   : ∀ x → [ single ] x IsRelatedTo x
  relTo : ∀ {x y} (x∼y : x ∼ y) → [ multi ] x IsRelatedTo y

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

-- Beginning of a proof

begin_ : ∀ {x y} → [ multi ] x IsRelatedTo y → x ∼ y
begin relTo x∼y = x∼y

-- Standard step with the relation

step-∼ : ∀ x {f y z} → [ f ] y IsRelatedTo z → x ∼ y → [ multi ] x IsRelatedTo z
step-∼ _ (emp _) x∼y     = relTo x∼y
step-∼ _ (relTo y∼z) x∼y = relTo (trans x∼y y∼z)

-- Step with a non-trivial propositional equality

step-≡ : ∀ x {f y z} → [ f ] y IsRelatedTo z → x ≡ y → [ f ] x IsRelatedTo z
step-≡ _ x∼z P.refl = x∼z

-- Step with a flipped non-trivial propositional equality

step-≡˘ : ∀ x {f y z} → [ f ] y IsRelatedTo z → y ≡ x → [ f ] x IsRelatedTo z
step-≡˘ _ x∼z P.refl = x∼z

-- -- Step with a trivial propositional equality

_≡⟨⟩_ : ∀ x {f y} → [ f ] x IsRelatedTo y → [ f ] x IsRelatedTo y
_ ≡⟨⟩ x∼y = x∼y

-- -- Termination step

_∎⟨_⟩ : ∀ x → x ∼ x → [ multi ] x IsRelatedTo x
_ ∎⟨ x∼x ⟩ = relTo x∼x

_∎ : ∀ x → [ single ] x IsRelatedTo x
_∎ = emp

-- Syntax declarations

syntax step-∼  x y∼z x∼y = x ∼⟨  x∼y ⟩ y∼z
syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z
