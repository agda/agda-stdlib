------------------------------------------------------------------------
-- The Agda standard library
--
-- Some examples showing how the Function.Reasoning.Logical module
-- can be used to make proofs more readable.
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}

module README.Function.LogicalReasoning where

open import Function.Reasoning.Logical

------------------------------------------------------------------------
-- A simple example

module _ {A B C : Set} {A⇒B : A → B} {B⇒C : B → C} where

-- Using the combinators we can, starting from a value, chain various
-- functions whilst tracking the types of the intermediate results.

  A⇒C : A → C
  A⇒C a = begin⟨ a ⟩ ⇒ A
    ∴⟨ A⇒B ⟩ ⇒ B
    ∴⟨ B⇒C ⟩ ⇒ C ∎

------------------------------------------------------------------------
-- A more concrete example

-- Will add a better example involving LCM once done
