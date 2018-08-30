------------------------------------------------------------------------
-- The Agda standard library
--
-- Base definitions for the left-biased universe-sensitive functor and
-- monad instances for These.
--
-- To minimize the universe level of the RawFunctor, we require that
-- elements of B are "lifted" to a copy of B at a higher universe level
-- (a ⊔ b).
-- See the Data.Product.Categorical.Examples for how this is done in a
-- Product-based similar setting.
------------------------------------------------------------------------

open import Level

module Data.These.Categorical.Left.Base {a} (A : Set a) (b : Level) where

open import Data.These
open import Category.Functor

Theseₗ : Set (a ⊔ b) → Set (a ⊔ b)
Theseₗ B = These A B

functor : RawFunctor Theseₗ
functor = record { _<$>_ = map₂ }
