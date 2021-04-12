------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of the lexicographic product of two operators.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core using (Op₂)
open import Data.Bool.Base using (true; false)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (does; yes; no)

module Algebra.Construct.LexProduct.Base
  {a b ℓ} {A : Set a} {B : Set b}
  (_∙_ : Op₂ A) (_◦_ : Op₂ B)
  {_≈₁_ : Rel A ℓ} (_≟₁_ : Decidable _≈₁_)
  where

------------------------------------------------------------------------
-- Definition

-- In order to get the first component to be definitionally equal to
-- `a ∙ b` and to simplify some of the proofs we first define an inner
-- operator that only calculates the second component of product.

innerLex : A → A → B → B → B
innerLex a b x y with does ((a ∙ b) ≟₁ a) | does ((a ∙ b) ≟₁ b)
... | true  | false = x
... | false | true  = y
... |     _ |     _ = x ◦ y

-- The full lexicographic choice operator can then be simply defined
-- in terms of the inner one.

lex : Op₂ (A × B)
lex (a , x) (b , y) = (a ∙ b , innerLex a b x y)
