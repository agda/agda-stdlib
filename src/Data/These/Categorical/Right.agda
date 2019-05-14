------------------------------------------------------------------------
-- The Agda standard library
--
-- Right-biased universe-sensitive functor and monad instances for These.
--
-- To minimize the universe level of the RawFunctor, we require that
-- elements of B are "lifted" to a copy of B at a higher universe level
-- (a ⊔ b).
-- See the Data.Product.Categorical.Examples for how this is done in a
-- Product-based similar setting.
------------------------------------------------------------------------

-- This functor can be understood as a notion of computation which can
-- either fail (that), succeed (this) or accumulate warnings whilst
-- delivering a successful computation (these).

-- It is a good alternative to Data.Product.Categorical when the notion
-- of warnings does not have a neutral element (e.g. List⁺).

{-# OPTIONS --without-K --safe #-}

open import Level
open import Algebra

module Data.These.Categorical.Right (a : Level) {c ℓ} (W : Semigroup c ℓ) where

open Semigroup W
open import Data.These.Categorical.Right.Base a Carrier public

open import Data.These
open import Category.Applicative
open import Category.Monad

module _ {a b} {A : Set a} {B : Set b} where

applicative : RawApplicative Theseᵣ
applicative = record
  { pure = this
  ; _⊛_  = ap
  } where

  ap : ∀ {A B}→ Theseᵣ (A → B) → Theseᵣ A → Theseᵣ B
  ap (this f)    t = map₁ f t
  ap (that w)    t = that w
  ap (these f w) t = map f (w ∙_) t

monad : RawMonad Theseᵣ
monad = record
  { return = this
  ; _>>=_  = bind
  } where

  bind : ∀ {A B} → Theseᵣ A → (A → Theseᵣ B) → Theseᵣ B
  bind (this t)    f = f t
  bind (that w)    f = that w
  bind (these t w) f = map₂ (w ∙_) (f t)
