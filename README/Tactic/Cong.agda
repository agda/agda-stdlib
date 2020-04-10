------------------------------------------------------------------------
-- The Agda standard library
--
-- Examples of how to use Tactic.Cong
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README.Tactic.Cong where

-- Tactic.Cong provides a helper macro for using congruence when reasoning about
-- relations. It allows the "hole" that you are operating in to be inferred from
-- the relation instance you are operating on, through use of ⌊_⌋.

-- Tactic.Cong is inspired by the agda-holes project.

-- For this README, the relation used is _≡_, though any (non-dependent) relation
-- with congruence and transitivity defined should work
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

--import this to use ⌊_⌋
open import Tactic.Cong.Id

-- import this to use ⌊⌋ , lhs , rhs and _≡⌊_⌋_
-- Arguments supplied:
--  * Recursion upper limit when evaluating reflected terms - typically does not
--    need to be large, and mostly depends on the cong and trans supplied, not
--    the equations you want to use this in.
--  * Relation that congruence operates over
--  * The congruence definition itself
--  * Transitivity definition for _≡_. Needed for _≡⌊_⌋_
open import Tactic.Cong 1 _≡_ cong trans

-- To use this tactic with _≡_ and cong from Cubical Agda, use
-- something like the following:
--
-- open import Tactic.Cong 2 _≡_ (λ f p → cong f p) _∙_

-- The following proofs show example uses of the macros ⌊⌋ and _≡⌊_⌋_
-- See Tactic.Cong for more details of how to use these macros

open import Data.Integer
open import Data.Integer.Properties
open import Function.Base

foo : (a b c d : ℤ) → (a + b) * (c + d) ≡ a * c + a * d + b * c + b * d
foo a b c d = begin
  (a + b) * (c + d)                   ≡⟨ *-distribˡ-+ (a + b) _ _ ⟩
  ⌊ (a + b) * c ⌋ + (a + b) * d       ≡⌊ *-distribʳ-+ c a b ⌋
  a * c + b * c + ⌊ (a + b) * d ⌋     ≡⌊ *-distribʳ-+ d a b ⌋
  a * c + b * c + (a * d + b * d)     ≡⟨ +-assoc (a * c) _ _ ⟩
  a * c + ⌊ b * c + (a * d + b * d)⌋  ≡⌊ +-comm (b * c) _ ⌋
  a * c + ((a * d + b * d) + b * c)   ≡⟨ sym $ +-assoc (a * c) _ _ ⟩
  ⌊ a * c + (a * d + b * d) ⌋ + b * c ≡⌊ sym $ +-assoc (a * c) _ _ ⌋
  a * c + a * d + b * d + b * c       ≡⟨ +-assoc (a * c + a * d) _ _ ⟩
  a * c + a * d + ⌊ b * d + b * c ⌋   ≡⌊ +-comm (b * d) _ ⌋
  a * c + a * d + (b * c + b * d)     ≡⟨ sym $ +-assoc (a * c + a * d) _ _ ⟩
  a * c + a * d + b * c + b * d       ∎

bar : (a b c : ℤ) → a + b + c ≡ b + a + c
bar a b c = begin
  ⌊ a + b ⌋ + c ≡⌊ +-comm a b ⌋
  b + a + c ∎

baz : (a b c : ℤ) → ⌊ a + b ⌋ + c ≡ b + a + c
baz a b c = ⌊⌋ lhs (+-comm a b)
