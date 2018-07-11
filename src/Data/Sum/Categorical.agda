------------------------------------------------------------------------
-- The Agda standard library
--
-- Universe-sensitive functor and monad instances for the Sum type.
------------------------------------------------------------------------

module Data.Sum.Categorical where

open import Level
open import Data.Sum
open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Function

-- To minimize the universe level of the RawFunctor, we require that elements of
-- B are "lifted" to a copy of B at a higher universe level (a ⊔ b). See the
-- examples for how this is done.

module Sumₗ {a} (A : Set a) (b : Level) where

  Sumₗ : Set (a ⊔ b) → Set (a ⊔ b)
  Sumₗ B = A ⊎ B

  functor : RawFunctor Sumₗ
  functor = record { _<$>_ = map₂ }

  applicative : RawApplicative Sumₗ
  applicative = record
    { pure = inj₂
    ; _⊛_ = [ const ∘ inj₁ , map₂ ]′
    }

  -- The monad instance also requires some mucking about with universe levels.
  monad : RawMonad Sumₗ
  monad = record
    { return = inj₂
    ; _>>=_  = [ const ∘ inj₁ , _|>′_ ]′
    }

-- The following are the "right-handed" versions

module Sumᵣ (a : Level) {b} (B : Set b) where

  Sumᵣ : Set (a ⊔ b) → Set (a ⊔ b)
  Sumᵣ A = A ⊎ B

  functor : RawFunctor Sumᵣ
  functor = record { _<$>_ = map₁ }

  applicative : RawApplicative Sumᵣ
  applicative = record
    { pure = inj₁
    ; _⊛_ = [ map₁ , const ∘ inj₂ ]′
    }

  monad : RawMonad Sumᵣ
  monad = record
    { return = inj₁
    ; _>>=_  = [ _|>′_ , const ∘ inj₂ ]′
    }

------------------------------------------------------------------------
-- Examples

-- Note that these examples are simple unit tests, because the type
-- checker verifies them.

private
  module Examples {a b} {A : Set a} {B : Set b} where

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
