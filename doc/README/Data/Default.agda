------------------------------------------------------------------------
-- The Agda standard library
--
-- An example showing how to define a function taking an optional
-- argument that default to a specified value if none is passed.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module README.Data.Default where

open import Data.Default
open import Data.Nat.Base hiding (_!)
open import Relation.Binary.PropositionalEquality

-- An argument of type `WithDefault {a} {A} x` is an argument of type
-- `A` that happens to default to `x` if no other value is specified

-- Note that you will only get this behaviour if the `default` instance
-- is in scope so you should either import `Data.Default` in your client
-- modules or publicly re-export the type and the instance!

-- `inc` increments its argument by the value `step`, defaulting to 1
inc : {{step : WithDefault 1}} → ℕ → ℕ
inc {{step}} n = step .value + n

-- and indeed incrementing 2 gives you 3
_ : inc 2 ≡ 3
_ = refl

-- but you can also insist that you want to use a bigger increment by
-- passing the `step` argument explicitly
_ : inc {{10 !}} 2 ≡ 12
_ = refl
