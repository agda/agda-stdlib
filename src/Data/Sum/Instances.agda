------------------------------------------------------------------------
-- The Agda standard library
--
-- Universe-sensitive functor and monad instances for the Sum type, in the
-- style of Haskell's Either.
------------------------------------------------------------------------

module Data.Sum.Instances where

-- Following Haskell convention, the inj₁ part of the sum is reserved
-- for "error" values, where as inj₂ represents a "normal" value.

open import Level
open import Data.Sum
open import Category.Functor
open import Category.Monad

-- To minimize the universe level of the RawFunctor, we require that elements of
-- B are "lifted" to a copy of B at a higher universe level (a ⊔ b). See the
-- examples for how this is done.
functor : ∀ {a} (A : Set a) → (b : Level)
        → RawFunctor {a ⊔ b} (λ (B : Set (a ⊔ b)) → A ⊎ B)
functor A b = record
  { _<$>_ = λ f x → helper f x }
  where
    helper : ∀ {B C} → (B → C) → A ⊎ B → A ⊎ C
    helper f (inj₁ x) = (inj₁ x)
    helper f (inj₂ y) = (inj₂ (f y))

-- The monad instance also requires some mucking about with universe levels.
monad : ∀ {a} (A : Set a) → (b : Level)
      → RawMonad {a ⊔ b} (λ (B : Set (a ⊔ b)) → A ⊎ B)
monad A b = record
  { return = λ x → inj₂ x
  ; _>>=_  = λ x f → helper x f
  }
  where
    helper : ∀ {B C} → A ⊎ B → (B → A ⊎ C) → A ⊎ C
    helper (inj₁ x) f = inj₁ x
    helper (inj₂ y) f = f y

------------------------------------------------------------------------
-- Examples

-- Note that these examples are simple unit tests, because the type
-- checker verifies them.

private
  module Examples {a b} {A : Set a} {B : Set b} where

    open import Agda.Builtin.Equality
    open import Function

    open RawFunctor {a ⊔ b} (functor A b)

    -- This type to the right of ⊎ needs to be a "lifted" version of (B : Set b)
    -- that lives in the universe (Set (a ⊔ b)).
    fmapId : (x : A ⊎ (Lift {ℓ = a} B)) → (id <$> x) ≡ x
    fmapId (inj₁ x) = refl
    fmapId (inj₂ y) = refl

    open RawMonad   {a ⊔ b} (monad A b)

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
