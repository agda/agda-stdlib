------------------------------------------------------------------------
-- The Agda standard library
--
-- An example of how Algebra.CommutativeMonoidSolver can be used
------------------------------------------------------------------------

module Algebra.Solver.CommutativeMonoid.Example where

open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Bool.Base using (_∨_)
open import Data.Bool.Properties using (∨-commutativeMonoid)

open import Data.Fin using (zero; suc)
open import Data.Vec using ([]; _∷_)

open import Algebra.Solver.CommutativeMonoid ∨-commutativeMonoid

test : ∀ x y z → (x ∨ y) ∨ (x ∨ z) ≡ (z ∨ y) ∨ (x ∨ x)
test a b c = let _∨_ = _⊕_ in
  prove 3 ((x ∨ y) ∨ (x ∨ z)) ((z ∨ y) ∨ (x ∨ x)) (a ∷ b ∷ c ∷ [])
  where
  x = var zero
  y = var (suc zero)
  z = var (suc (suc zero))
