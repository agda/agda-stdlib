------------------------------------------------------------------------
-- The Agda standard library
--
-- Some examples showing magma reasoning can be used
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README.Algebra.Reasoning.Magma where

open import Data.Nat
open import Data.Nat.Properties using (+-magma)
open import Relation.Binary.PropositionalEquality

-- Suppose we want to prove a result such as if x ≡ y' and z ≡ z'
-- then (x + y) + (x + z) ≡ (x + y') + (x + z')

-- A normal proof might look something like:

normal-proof : ∀ x y y' z z' → x + y ≡ y' → z' ≡ z →
                 (x + y) + (x + z) ≡ y' + (x + z')
normal-proof x y y' z z' x+y≡y' z'≡z =
  cong₂ _+_ x+y≡y' (cong₂ _+_ refl (sym z'≡z))

-- Using magma reasoning we can do something like:

open import Algebra.Reasoning.Magma (+-magma)
open import Algebra.Bundles
open Magma +-magma

new-proof : ∀ x y y' z z' → x + y ≡ y' → z' ≡ z →
              (x + y) + (x + z) ≡ y' + (x + z')
new-proof x y y' z z' x+y≡y' z'≡z = begin
  ⌊ x ∙ y ⌋ ▸ (x ∙ z)  ≈⌊  x+y≡y' ⌋
  y' ◂ (x ◂ ⌊ z ⌋)     ≈˘⌊ z'≡z   ⌋
  y' ∙ (x ∙ z')        ∎

-- Magma reasoning works by having an Expr object on the lhs.
-- An Expr object is a tree with a focus on one of the leaves.
-- Magma reasoning then allows you apply an equality to the focus
-- without having to manually specify the congs

-- _◂_ _▸_ and ⌊_⌋ are used to build Expr objects. ⌊_⌋ creates a leaf
-- which is focused. _◂_ and _▸_ attach a leaf to the left or right
-- side of an Expr object.
