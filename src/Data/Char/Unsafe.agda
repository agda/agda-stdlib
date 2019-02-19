------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe Char operations and proofs
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}

module Data.Char.Unsafe where

open import Data.Bool.Base using (Bool; true; false)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary using (Decidable; DecSetoid)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe

open import Agda.Builtin.Char using (primCharEquality)
open import Data.Char

------------------------------------------------------------------------
-- An informative equality test.

infix 4 _≟_

_≟_ : Decidable {A = Char} _≡_
s₁ ≟ s₂ with primCharEquality s₁ s₂
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

------------------------------------------------------------------------
-- Boolean equality test.
--
-- Why is the definition _==_ = primCharEquality not used? One reason
-- is that the present definition can sometimes improve type
-- inference, at least with the version of Agda that is current at the
-- time of writing: see unit-test below.

infix 4 _==_

_==_ : Char → Char → Bool
c₁ == c₂ = ⌊ c₁ ≟ c₂ ⌋

private

  -- The following unit test does not type-check (at the time of
  -- writing) if _==_ is replaced by primCharEquality.

  data P : (Char → Bool) → Set where
    p : (c : Char) → P (c ==_)

  unit-test : P ('x' ==_)
  unit-test = p _

------------------------------------------------------------------------
-- Decidable equality

decSetoid : DecSetoid _ _
decSetoid = PropEq.decSetoid _≟_
