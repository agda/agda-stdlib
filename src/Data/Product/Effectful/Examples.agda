------------------------------------------------------------------------
-- The Agda standard library
--
-- Universe-sensitive functor and monad instances for the Product type.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra

module Data.Product.Effectful.Examples
  {a e b} {A : Monoid a e} {B : Set b} where

open import Level using (Lift; lift; _⊔_)
open import Effect.Functor using (RawFunctor)
open import Effect.Monad using (RawMonad)
open import Data.Product.Base using (_×_; _,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Function.Base using (id)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

------------------------------------------------------------------------
-- Examples

-- Note that these examples are simple unit tests, because the type
-- checker verifies them.

private

  module A = Monoid A

  open import Data.Product.Effectful.Left A.rawMonoid b

  _≈_ : Rel (A.Carrier × Lift a B) (e ⊔ a ⊔ b)
  _≈_ = Pointwise A._≈_ _≡_

  open RawFunctor functor

  -- This type to the right of × needs to be a "lifted" version of
  -- (B : Set b) that lives in the universe (Set (a ⊔ b)).
  fmapIdₗ : (x : A.Carrier × Lift a B) → (id <$> x) ≈ x
  fmapIdₗ x = A.refl , refl

  open RawMonad monad

  -- Now, let's show that "pure" is a unit for >>=. We use Lift in
  -- exactly the same way as above. The data (x : B) then needs to be
  -- "lifted" to this new type (Lift B).
  pureUnitL : ∀ {x : B} {f : Lift a B → A.Carrier × Lift a B} →
                (pure (lift x) >>= f) ≈ f (lift x)
  pureUnitL = A.identityˡ _ , refl

  pureUnitR : {x : A.Carrier × Lift a B} → (x >>= pure) ≈ x
  pureUnitR = A.identityʳ _ , refl

  -- And another (limited version of a) monad law...
  bindCompose : ∀ {f g : Lift a B → A.Carrier × Lift a B} →
                {x : A.Carrier × Lift a B} →
                ((x >>= f) >>= g) ≈ (x >>= (λ y → (f y >>= g)))
  bindCompose = A.assoc _ _ _ , refl
