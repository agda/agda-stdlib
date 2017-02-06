------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe functions on strings
------------------------------------------------------------------------

module Unsafe.Data.String where

open import Data.String public

open import Data.Bool.Base using (Bool ; true ; false)
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Binary
open import Unsafe.Relation.Binary.PropositionalEquality.TrustMe
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)


-- Informative equality test.

infix 4 _≟_

_≟_ : Decidable {A = String} _≡_
s₁ ≟ s₂ with primStringEquality s₁ s₂
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

-- Boolean equality test.
--
-- Why is the definition _==_ = primStringEquality not used? One
-- reason is that the present definition can sometimes improve type
-- inference, at least with the version of Agda that is current at the
-- time of writing: see unit-test below.

infix 4 _==_

_==_ : String → String → Bool
s₁ == s₂ = ⌊ s₁ ≟ s₂ ⌋

private

  -- The following unit test does not type-check (at the time of
  -- writing) if _==_ is replaced by primStringEquality.

  data P : (String → Bool) → Set where
    p : (c : String) → P (_==_ c)

  unit-test : P (_==_ "")
  unit-test = p _

decSetoid : DecSetoid _ _
decSetoid = PropEq.decSetoid _≟_

