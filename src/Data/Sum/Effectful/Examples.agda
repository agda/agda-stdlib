------------------------------------------------------------------------
-- The Agda standard library
--
-- Usage examples of the effectful view of the Sum type
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Sum.Effectful.Examples where

open import Level
open import Data.Sum.Base
import Data.Sum.Effectful.Left as Sumₗ
open import Effect.Functor
open import Effect.Monad

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

    -- Now, let's show that "pure" is a unit for >>=. We use Lift in exactly
    -- the same way as above. The data (x : B) then needs to be "lifted" to
    -- this new type (Lift B).
    pureUnitL : ∀ {x : B} {f : Lift a B → A ⊎ (Lift a B)}
                  → (pure (lift x) >>= f) ≡ f (lift x)
    pureUnitL = refl

    pureUnitR : (x : A ⊎ (Lift a B)) → (x >>= pure) ≡ x
    pureUnitR (inj₁ _) = refl
    pureUnitR (inj₂ _) = refl

    -- And another (limited version of a) monad law...
    bindCompose : ∀ {f g : Lift a B → A ⊎ (Lift a B)}
                → (x : A ⊎ (Lift a B))
                → ((x >>= f) >>= g) ≡ (x >>= (λ y → (f y >>= g)))
    bindCompose (inj₁ x) = refl
    bindCompose (inj₂ y) = refl
