{-# OPTIONS --cubical-compatible --safe #-}

module README.Tactic.CaseBash where

open import Algebra.Definitions
open import Relation.Binary.PropositionalEquality

----------------------------------------------------------------------
-- Usage
----------------------------------------------------------------------

-- When working with non-recursive datatypes, it's common to define
-- functions by exhaustively pattern matching. This is exacerbated
-- by the restrictions that case-trees place on fall-through patterns;
-- such functions do not have good definitional behaviour

-- For example:

data Foo : Set where
  foo bar baz : Foo

go : Foo → Foo → Foo
go foo _ = foo
go _ foo = foo
go bar _ = bar
go _ bar = bar
go baz baz = baz

-- Writing these functions is tedious, but reasoning about them is
-- even worse. Proofs consist of casing on every single argument, and
-- then proving the goal with 'refl' on the RHS.

go-comm : Commutative _≡_ go
go-comm foo foo = refl
go-comm foo bar = refl
go-comm foo baz = refl
go-comm bar foo = refl
go-comm baz foo = refl
go-comm bar bar = refl
go-comm bar baz = refl
go-comm baz bar = refl
go-comm baz baz = refl

-- The 'case-bash!' tactic automates this tedium away by case splitting
-- on every argument, and then attempting to prove the goal with refl.
-- This allows us to make quick work of some easy proofs.

open import Tactic.CaseBash using (caseBash!)

go-comm-bash : Commutative _≡_ go
go-comm-bash = caseBash!
