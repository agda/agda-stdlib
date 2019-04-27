------------------------------------------------------------------------
-- The Agda standard library
--
-- The type for booleans and some operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bool.Base where

open import Data.Unit.Base using (⊤)
open import Data.Empty
open import Level using (Level)
open import Relation.Nullary

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- The boolean type

open import Agda.Builtin.Bool public

------------------------------------------------------------------------
-- Boolean operations

infixr 6 _∧_
infixr 5 _∨_ _xor_

not : Bool → Bool
not true  = false
not false = true

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ b = false

_∨_ : Bool → Bool → Bool
true  ∨ b = true
false ∨ b = b

_xor_ : Bool → Bool → Bool
true  xor b = not b
false xor b = b

------------------------------------------------------------------------
-- Other operations

infix  0 if_then_else_

if_then_else_ : Bool → A → A → A
if true  then t else f = t
if false then t else f = f

-- A function mapping true to an inhabited type and false to an empty
-- type.

T : Bool → Set
T true  = ⊤
T false = ⊥

