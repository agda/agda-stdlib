------------------------------------------------------------------------
-- The Agda standard library
--
-- Universe-sensitive functor and monad instances for the Product type.
------------------------------------------------------------------------

open import Algebra

module Data.Product.Categorical.Examples
  {a e b} {A : Monoid a e} {B : Set b} where

open import Level using (Lift; lift; _⊔_)
open import Category.Functor using (RawFunctor)
open import Category.Monad using (RawMonad)
open import Data.Product
open import Data.Product.Relation.Pointwise.NonDependent
open import Function
import Function.Identity.Categorical as Id
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Examples

-- Note that these examples are simple unit tests, because the type
-- checker verifies them.

private

  module A = Monoid A

  open import Data.Product.Categorical.Left A.rawMonoid b

  _≈_ : Rel (A.Carrier × Lift a B) (e ⊔ a ⊔ b)
  _≈_ = Pointwise A._≈_ _≡_

  open RawFunctor functor

  -- This type to the right of × needs to be a "lifted" version of (B : Set b)
  -- that lives in the universe (Set (a ⊔ b)).
  fmapIdₗ : (x : A.Carrier × Lift a B) → (id <$> x) ≈ x
  fmapIdₗ x = A.refl , refl

  open RawMonad monad

  -- Now, let's show that "return" is a unit for >>=. We use Lift in exactly
  -- the same way as above. The data (x : B) then needs to be "lifted" to
  -- this new type (Lift B).
  returnUnitL : ∀ {x : B} {f : Lift a B → A.Carrier × Lift a B} →
                ((return (lift x)) >>= f) ≈ f (lift x)
  returnUnitL = A.identityˡ _ , refl

  returnUnitR : {x : A.Carrier × Lift a B} → (x >>= return) ≈ x
  returnUnitR = A.identityʳ _ , refl

  -- And another (limited version of a) monad law...
  bindCompose : ∀ {f g : Lift a B → A.Carrier × Lift a B} →
                {x : A.Carrier × Lift a B} →
                ((x >>= f) >>= g) ≈ (x >>= (λ y → (f y >>= g)))
  bindCompose = A.assoc _ _ _ , refl
