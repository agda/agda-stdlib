------------------------------------------------------------------------
-- The Agda standard library
--
-- Usage examples of the categorical view of the Sum type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Categorical.Examples where

open import Level
open import Data.Sum.Base
import Data.Sum.Categorical.Left as Sumₗ
open import Category.Functor
open import Category.Monad

-- Note that these examples are simple unit tests, because the type
-- checker verifies them.

private
  module Examplesₗ {a b} {A : Set a} {B : Set b} where

    open import Agda.Builtin.Equality
    open import Function
    module Sₗ = Sumₗ A b

    open RawFunctor Sₗ.functor

    -- This type to the right of ⊎ needs to be a "lifted" version of (B : Set b)
    -- that lives in the universe (Set (a ⊔ b)).
    fmapId : (x : A ⊎ (Lift a B)) → (id <$> x) ≡ x
    fmapId (inj₁ x) = refl
    fmapId (inj₂ y) = refl


    open RawMonad   Sₗ.monad

    -- Now, let's show that "return" is a unit for >>=. We use Lift in exactly
    -- the same way as above. The data (x : B) then needs to be "lifted" to
    -- this new type (Lift B).
    returnUnitL : ∀ {x : B} {f : Lift a B → A ⊎ (Lift a B)}
                  → ((return (lift x)) >>= f) ≡ f (lift x)
    returnUnitL = refl

    returnUnitR : (x : A ⊎ (Lift a B)) → (x >>= return) ≡ x
    returnUnitR (inj₁ _) = refl
    returnUnitR (inj₂ _) = refl

    -- And another (limited version of a) monad law...
    bindCompose : ∀ {f g : Lift a B → A ⊎ (Lift a B)}
                → (x : A ⊎ (Lift a B))
                → ((x >>= f) >>= g) ≡ (x >>= (λ y → (f y >>= g)))
    bindCompose (inj₁ x) = refl
    bindCompose (inj₂ y) = refl
