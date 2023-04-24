------------------------------------------------------------------------
-- The Agda standard library
--
-- A way to specify that a function's argument takes a default value
-- if the argument is not passed explicitly.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

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

-- See README.Data.Default for an example
