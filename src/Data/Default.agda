------------------------------------------------------------------------
-- The Agda standard library
--
-- A way to specify that a function's argument takes a default value
-- if the argument is not passed explicitly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Default where

-- An argument of type `WithDefault {a} {A} x` is an argument of type
-- `A` that happens to default to `x` if no other value is specified
-- (as long as the `default` instance is in scope)

infixl 0 _!
record WithDefault {a} {A : Set a} (x : A) : Set a where
  constructor _!
  field value : A
open WithDefault public

instance
  default : ∀ {a} {A : Set a} {x : A} → WithDefault x
  default {x = x} .value = x



------------------------------------------------------------------------
-- Example
------------------------------------------------------------------------

private

  open import Agda.Builtin.Nat
  open import Agda.Builtin.Equality

  -- `inc` increments its argument by the value `step`, defaulting to 1
  inc : {{step : WithDefault 1}} → Nat → Nat
  inc {{step}} n = step .value + n

  -- and indeed incrementing 2 gives you 3
  _ : inc 2 ≡ 3
  _ = refl

  -- but you can also insist that you want to use a bigger increment by
  -- passing the `step` argument explicitly
  _ : inc {{10 !}} 2 ≡ 12
  _ = refl
