------------------------------------------------------------------------
-- The Agda standard library
--
-- Right-biased universe-sensitive functor and monad instances for These.
------------------------------------------------------------------------

-- To minimize the universe level of the RawFunctor, we require that
-- elements of B are "lifted" to a copy of B at a higher universe level
-- (a ⊔ b).
-- See the Data.Product.Effectful.Examples for how this is done in a
-- Product-based similar setting.

-- This functor can be understood as a notion of computation which can
-- either fail (that), succeed (this) or accumulate warnings whilst
-- delivering a successful computation (these).

-- It is a good alternative to Data.Product.Effectful when the notion
-- of warnings does not have a neutral element (e.g. List⁺).

{-# OPTIONS --cubical-compatible --safe #-}

open import Level using (Level; _⊔_)
open import Algebra.Bundles using (Semigroup)

module Data.These.Effectful.Right (a : Level) {c ℓ} (W : Semigroup c ℓ) where

open import Data.These.Base using (These; this; that; these; map₁; map₂; map)
open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad)

open Semigroup W
open import Data.These.Effectful.Right.Base a Carrier public

module _ {a b} {A : Set a} {B : Set b} where

applicative : RawApplicative Theseᵣ
applicative = record
  { rawFunctor = functor
  ; pure = this
  ; _<*>_  = ap
  } where

  ap : ∀ {A B}→ Theseᵣ (A → B) → Theseᵣ A → Theseᵣ B
  ap (this f)    t = map₁ f t
  ap (that w)    t = that w
  ap (these f w) t = map f (w ∙_) t

monad : RawMonad Theseᵣ
monad = record
  { rawApplicative = applicative
  ; _>>=_  = bind
  } where

  bind : ∀ {A B} → Theseᵣ A → (A → Theseᵣ B) → Theseᵣ B
  bind (this t)    f = f t
  bind (that w)    f = that w
  bind (these t w) f = map₂ (w ∙_) (f t)
