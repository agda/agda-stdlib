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

module _ {a} (A : Set a) (b : Level) where

  Sumₗ : Set (a ⊔ b) → Set (a ⊔ b)
  Sumₗ B = A ⊎ B

  functorₗ : RawFunctor Sumₗ
  functorₗ = record { _<$>_ = map id }

  applicativeₗ : RawApplicative Sumₗ
  applicativeₗ = record
    { pure = inj₂
    ; _⊛_ = [ const ∘ inj₁ , map id ]′
    }

  -- The monad instance also requires some mucking about with universe levels.
  monadₗ : RawMonad Sumₗ
  monadₗ = record
    { return = inj₂
    ; _>>=_  = [ const ∘ inj₁ , _|>′_ ]′
    }

-- The following are the "right-handed" versions

module _ (a : Level) {b} (B : Set b) where

  Sumᵣ : Set (a ⊔ b) → Set (a ⊔ b)
  Sumᵣ A = A ⊎ B

  functorᵣ : RawFunctor Sumᵣ
  functorᵣ = record { _<$>_ = λ f → map f id }

  applicativeᵣ : RawApplicative Sumᵣ
  applicativeᵣ = record
    { pure = inj₁
    ; _⊛_ = [ flip map id , const ∘ inj₂ ]′
    }

  monadᵣ : RawMonad Sumᵣ
  monadᵣ = record
    { return = inj₁
    ; _>>=_  = λ x f → [ f , inj₂ ]′ x
    }

------------------------------------------------------------------------
-- Examples

-- Note that these examples are simple unit tests, because the type
-- checker verifies them.

private
  module Examplesₗ {a b} {A : Set a} {B : Set b} where

    open import Agda.Builtin.Equality
    open import Function

    open RawFunctor {a ⊔ b} (functorₗ A b)

    -- This type to the right of ⊎ needs to be a "lifted" version of (B : Set b)
    -- that lives in the universe (Set (a ⊔ b)).
    fmapIdₗ : (x : A ⊎ (Lift {ℓ = a} B)) → (id <$> x) ≡ x
    fmapIdₗ (inj₁ x) = refl
    fmapIdₗ (inj₂ y) = refl


    open RawMonad   {a ⊔ b} (monadₗ A b)

    -- Now, let's show that "return" is a unit for >>=. We use Lift in exactly
    -- the same way as above. The data (x : B) then needs to be "lifted" to
    -- this new type (Lift B).
    returnUnitL : ∀ {x : B} {f : Lift {ℓ = a} B → A ⊎ (Lift {ℓ = a} B)}
                  → ((return (lift x)) >>= f) ≡ f (lift x)
    returnUnitL = refl

    returnUnitR : (x : A ⊎ (Lift {ℓ = a} B)) → (x >>= return) ≡ x
    returnUnitR (inj₁ _) = refl
    returnUnitR (inj₂ _) = refl

    -- And another (limited version of a) monad law...
    bindCompose : ∀ {f g : Lift {ℓ = a} B → A ⊎ (Lift {ℓ = a} B)}
                → (x : A ⊎ (Lift {ℓ = a} B))
                → ((x >>= f) >>= g) ≡ (x >>= (λ y → (f y >>= g)))
    bindCompose (inj₁ x) = refl
    bindCompose (inj₂ y) = refl
