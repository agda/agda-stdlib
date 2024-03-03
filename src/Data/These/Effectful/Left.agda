------------------------------------------------------------------------
-- The Agda standard library
--
-- Left-biased universe-sensitive functor and monad instances for These.
--
------------------------------------------------------------------------

-- To minimize the universe level of the RawFunctor, we require that
-- elements of B are "lifted" to a copy of B at a higher universe level
-- (a ⊔ b).
-- See the Data.Product.Effectful.Examples for how this is done in a
-- Product-based similar setting.

-- This functor can be understood as a notion of computation which can
-- either fail (this), succeed (that) or accumulate warnings whilst
-- delivering a successful computation (these).

-- It is a good alternative to Data.Product.Effectful when the notion
-- of warnings does not have a neutral element (e.g. List⁺).

{-# OPTIONS --cubical-compatible --safe #-}

open import Level
open import Algebra

module Data.These.Effectful.Left {c ℓ} (W : Semigroup c ℓ) (b : Level) where

open Semigroup W
open import Data.These.Effectful.Left.Base Carrier b public

open import Data.These.Base
open import Effect.Applicative
open import Effect.Monad

module _ {a b} {A : Set a} {B : Set b} where

applicative : RawApplicative Theseₗ
applicative = record
  { rawFunctor = functor
  ; pure = that
  ; _<*>_  = ap
  } where

  ap : ∀ {A B} → Theseₗ (A → B) → Theseₗ A → Theseₗ B
  ap (this w)    t = this w
  ap (that f)    t = map₂ f t
  ap (these w f) t = map (w ∙_) f t

monad : RawMonad Theseₗ
monad = record
  { rawApplicative = applicative
  ; _>>=_  = bind
  } where

  bind : ∀ {A B} → Theseₗ A → (A → Theseₗ B) → Theseₗ B
  bind (this w)    f = this w
  bind (that t)    f = f t
  bind (these w t) f = map₁ (w ∙_) (f t)
