------------------------------------------------------------------------
-- The Agda standard library
--
-- Strict combinators (i.e. that use call-by-value)
------------------------------------------------------------------------

-- The contents of this module is also accessible via the `Function`
-- module.

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Strict where

open import Agda.Builtin.Equality using (_≡_)
open import Function.Base using (flip)
open import Level using (Level)

private
  variable
    a b : Level
    A B : Set a

infixl 0 _!|>_ _!|>′_
infixr -1 _$!_ _$!′_

------------------------------------------------------------------------
-- Dependent combinators

-- These are functions whose output has a type that depends on the
-- value of the input to the function.

open import Agda.Builtin.Strict public
  renaming
  ( primForce      to force
  ; primForceLemma to force-≡
  )

-- Application
_$!_ : ∀ {A : Set a} {B : A → Set b} →
       ((x : A) → B x) → ((x : A) → B x)
f $! x = force x f

-- Flipped application
_!|>_ : ∀ {A : Set a} {B : A → Set b} →
       (a : A) → (∀ a → B a) → B a
_!|>_ = flip _$!_

------------------------------------------------------------------------
-- Non-dependent combinators

-- Any of the above operations for dependent functions will also work
-- for non-dependent functions but sometimes Agda has difficulty
-- inferring the non-dependency. Primed (′ = \prime) versions of the
-- operations are therefore provided below that sometimes have better
-- inference properties.

seq : A → B → B
seq a b = force a (λ _ → b)

seq-≡ : (a : A) (b : B) → seq a b ≡ b
seq-≡ a b = force-≡ a (λ _ → b)

force′ : A → (A → B) → B
force′ = force

force′-≡ : (a : A) (f : A → B) → force′ a f ≡ f a
force′-≡ = force-≡

-- Application
_$!′_ : (A → B) → (A → B)
_$!′_ = _$!_

-- Flipped application
_!|>′_ : A → (A → B) → B
_!|>′_ = _!|>_
