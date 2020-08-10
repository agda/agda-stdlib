------------------------------------------------------------------------
-- The Agda standard library
--
-- Examples of how to use Tactic.Cong
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README.Tactic.Cong where

open import Relation.Binary.PropositionalEquality

-- Tactic.Cong provides a helper macro for using congruence when reasoning about
-- relations. It allows the "hole" that you are operating in to be inferred from
-- the relation instance you are operating on, through use of ⌞_⌟.

-- Tactic.Cong is inspired by the agda-holes project.

--import this to use ⌞_⌟ , lhs and rhs
open import Tactic.Cong.Common

open import Data.Integer
open import Data.Integer.Properties
open import Function.Base

-- Tactic.Cong is a very general parameterised module. Common use cases have
-- been bundled as sub-modules with fewer parameters.
-- Tactic.Cong.PropEq and its submodules use congruence of propositional
-- equality, which is the most common use case.
import Tactic.Cong.PropEq.ForAllTypes
import Tactic.Cong.PropEq.ForOneType

module _ where
  open ≡-Reasoning
  open Tactic.Cong.PropEq.ForAllTypes 0 _≡_ trans
  -- This use of Tactic.Cong.PropEq.ForAllTypes is equivalent to:
  --
  -- open Tactic.Cong 0 _≡_ cong ℓSet projₗ projₛ _≡_ trans renaming (_≈⌊_⌋_ to _≡⌊_⌋_)
  --
  -- The arguments supplied to the module are:
  -- * The recursion limit in the macro when evaluating the functions provided
  --   to the macro. This can normally be very low (e.g. 0), and does not depend
  --   on the complexity of terms used in your proofs. Increment it if you see
  --   an error of the form "Tactic.Cong: evaluation limit reached".
  -- * The type of the relation that "begin ... ∎" produces, which is not
  --   necessarily propositional equality (see the ≤-Reasoning proof below, for
  --   example).
  -- * A proof of transitivity of _≡_ with respect to the relation.

  -- example proofs using _≡⌊_⌋_ :

  foo : (a b c d : ℤ) → (a + b) * (c + d) ≡ a * c + a * d + b * c + b * d
  foo a b c d = begin
    (a + b) * (c + d)                   ≡⟨ *-distribˡ-+ (a + b) _ _ ⟩
    ⌞ (a + b) * c ⌟ + (a + b) * d       ≡⌊ *-distribʳ-+ c a b ⌋
    a * c + b * c + ⌞ (a + b) * d ⌟     ≡⌊ *-distribʳ-+ d a b ⌋
    a * c + b * c + (a * d + b * d)     ≡⟨ +-assoc (a * c) _ _ ⟩
    a * c + ⌞ b * c + (a * d + b * d)⌟  ≡⌊ +-comm (b * c) _ ⌋
    a * c + ((a * d + b * d) + b * c)   ≡⟨ sym $ +-assoc (a * c) _ _ ⟩
    ⌞ a * c + (a * d + b * d) ⌟ + b * c ≡⌊ sym $ +-assoc (a * c) _ _ ⌋
    a * c + a * d + b * d + b * c       ≡⟨ +-assoc (a * c + a * d) _ _ ⟩
    a * c + a * d + ⌞ b * d + b * c ⌟   ≡⌊ +-comm (b * d) _ ⌋
    a * c + a * d + (b * c + b * d)     ≡⟨ sym $ +-assoc (a * c + a * d) _ _ ⟩
    a * c + a * d + b * c + b * d       ∎

  bar : (a b c : ℤ) → a + b + c ≡ b + a + c
  bar a b c = begin
    ⌞ a + _ ⌟ + _ ≡⌊ +-comm a _ ⌋
    _             ∎

  baz : (a b c : ℤ) → ⌞ a + b ⌟ + c ≡ b + a + c
  baz a b c = ⌊⌋ lhs (+-comm a b)
  -- The use of lhs above tells the macro to look for ⌞_⌟ in the left hand side
  -- of the relation instance.

module _ where
  open ≤-Reasoning
  open Tactic.Cong.PropEq.ForOneType 0 _IsRelatedTo_ (λ {i = i} p q → step-≡ i q p)
  -- This use of Tactic.Cong.PropEq.ForOneType is equivalent to:
  --
  -- open Tactic.Cong 0 _≡_ cong ⊤ω (constω 0ℓ) (constω ℤ) _IsRelatedTo_ (λ {A} {i = i} p q → step-≡ i q p) renaming (_≈⌊_⌋_ to _≡⌊_⌋_)
  --
  -- This is similar to the use of Tactic.Cong.PropEq.ForAllTypes, but it works
  -- for relations that operate over only one specific type instead of any.

  -- example proof using _≡⌊_⌋_ :
  qu : (a b c d : ℤ) → a + b + c ≤ d → b + a + c ≤ d
  qu a b c d  a+b+c≤d = begin
    ⌞ b + a ⌟ + _ ≡⌊ +-comm b _ ⌋
    a + b + c     ≤⟨ a+b+c≤d ⟩
    d             ∎

-- Note: To use this Tactic.Cong with _≡_ and cong from Cubical Agda instead, use
-- something like the following:
--
-- open import Tactic.Cong 2 _≡_ ℓSet projₗ projₛ _∙_ renaming (_≈⌊_⌋_ to _≡⌊_⌋_)
