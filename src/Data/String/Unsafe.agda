------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe String operations and proofs
------------------------------------------------------------------------

module Data.String.Unsafe where

open import Data.String
open import Data.Bool.Base using (Bool; true; false)
open import Relation.Binary using (Decidable; DecSetoid)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

------------------------------------------------------------------------
-- An informative equality test.

infix 4 _≟_

_≟_ : Decidable {A = String} _≡_
s₁ ≟ s₂ with primStringEquality s₁ s₂
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

------------------------------------------------------------------------
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

------------------------------------------------------------------------
-- Equality

decSetoid : DecSetoid _ _
decSetoid = PropEq.decSetoid _≟_

------------------------------------------------------------------------
-- Other properties

toList∘fromList : ∀ s → toList (fromList s) ≡ s
toList∘fromList s = trustMe

fromList∘toList : ∀ s → fromList (toList s) ≡ s
fromList∘toList s = trustMe
