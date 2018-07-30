------------------------------------------------------------------------
-- The Agda standard library
--
-- Universe-sensitive functor and monad instances for the Product type.
------------------------------------------------------------------------

module Data.Product.Categorical where

open import Level
open import Data.Product
open import Algebra
open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Category.Monad.Identity
open import Category.Comonad
open import Function

-- To minimize the universe level of the RawFunctor, we require that elements of
-- B are "lifted" to a copy of B at a higher universe level (a ⊔ b). See the
-- examples for how this is done.

------------------------------------------------------------------------
-- Left-biased monad

module Baseₗ {a} (A : Set a) (b : Level) where

  Productₗ : Set (a ⊔ b) → Set (a ⊔ b)
  Productₗ B = A × B

  functor : RawFunctor Productₗ
  functor = record { _<$>_ = λ f → map₂ f }

  comonad : RawComonad Productₗ
  comonad = record
    { extract = proj₂
    ; extend  = < proj₁ ,_>
    }

module Productₗ {a e} (A : RawMonoid a e) (b : Level) where

  private module A = RawMonoid A
  open Baseₗ A.Carrier b public

  applicative : RawApplicative Productₗ
  applicative = record
    { pure = A.ε ,_
    ; _⊛_  = zip A._∙_ id
    }

  -- The monad instance also requires some mucking about with universe levels.
  monadT : ∀ {M} → RawMonad M → RawMonad (M ∘′ Productₗ)
  monadT M = record
    { return = M.pure ∘′ (A.ε ,_)
    ; _>>=_  = λ ma f → ma M.>>= uncurry λ a x → map₁ (a A.∙_) M.<$> f x
    } where module M = RawMonad M

  monad : RawMonad Productₗ
  monad = monadT IdentityMonad

------------------------------------------------------------------------
-- Get access to other monadic functions

  module _ {F} (App : RawApplicative {a ⊔ b} F) where

    open RawApplicative App

    sequenceA : ∀ {A} → Productₗ (F A) → F (Productₗ A)
    sequenceA (x , fa) = (x ,_) <$> fa

    mapA : ∀ {A B} → (A → F B) → Productₗ A → F (Productₗ B)
    mapA f = sequenceA ∘ map₂ f

    forA : ∀ {A B} → Productₗ A → (A → F B) → F (Productₗ B)
    forA = flip mapA

  module _ {M} (Mon : RawMonad {a ⊔ b} M) where

    private App = RawMonad.rawIApplicative Mon

    sequenceM : ∀ {A} → Productₗ (M A) → M (Productₗ A)
    sequenceM = sequenceA App

    mapM : ∀ {A B} → (A → M B) → Productₗ A → M (Productₗ B)
    mapM = mapA App

    forM : ∀ {A B} → Productₗ A → (A → M B) → M (Productₗ B)
    forM = forA App


------------------------------------------------------------------------
-- Right-biased monad

module Baseᵣ (a : Level) {b} (B : Set b) where

  Productᵣ : Set (a ⊔ b) → Set (a ⊔ b)
  Productᵣ A = A × B

  functor : RawFunctor Productᵣ
  functor = record { _<$>_ = map₁ }

  comonad : RawComonad Productᵣ
  comonad = record
    { extract = proj₁
    ; extend  = <_, proj₂ >
    }

module Productᵣ (a : Level) {b e} (B : RawMonoid b e) where

  private module B = RawMonoid B
  open Baseᵣ a B.Carrier public

  applicative : RawApplicative Productᵣ
  applicative = record
    { pure = _, B.ε
    ; _⊛_  = zip id B._∙_
    }

  monadT : ∀ {M} → RawMonad M → RawMonad (M ∘′ Productᵣ)
  monadT M = record
    { return = M.pure ∘′ (_, B.ε)
    ; _>>=_  = λ ma f → ma M.>>= uncurry λ x b → map₂ (b B.∙_) M.<$> f x
    } where module M = RawMonad M

  monad : RawMonad Productᵣ
  monad = monadT IdentityMonad

------------------------------------------------------------------------
-- Get access to other monadic functions

  module _ {F} (App : RawApplicative {a ⊔ b} F) where

    open RawApplicative App

    sequenceA : ∀ {A} → Productᵣ (F A) → F (Productᵣ A)
    sequenceA (fa , y) = (_, y) <$> fa

    mapA : ∀ {A B} → (A → F B) → Productᵣ A → F (Productᵣ B)
    mapA f = sequenceA ∘ map₁ f

    forA : ∀ {A B} → Productᵣ A → (A → F B) → F (Productᵣ B)
    forA = flip mapA

  module _ {M} (Mon : RawMonad {a ⊔ b} M) where

    private App = RawMonad.rawIApplicative Mon

    sequenceM : ∀ {A} → Productᵣ (M A) → M (Productᵣ A)
    sequenceM = sequenceA App

    mapM : ∀ {A B} → (A → M B) → Productᵣ A → M (Productᵣ B)
    mapM = mapA App

    forM : ∀ {A B} → Productᵣ A → (A → M B) → M (Productᵣ B)
    forM = forA App

------------------------------------------------------------------------
-- Examples

-- Note that these examples are simple unit tests, because the type
-- checker verifies them.

private
  module Examplesₗ {a e b} {A : Monoid a e} {B : Set b} where

    open import Agda.Builtin.Equality
    open import Relation.Binary.Core
    open import Data.Product.Relation.Pointwise.NonDependent
    open import Function
    module A = Monoid A
    module Pₗ = Productₗ A.rawMonoid b

    _≈_ : Rel (A.Carrier × Lift a B) (e ⊔ a ⊔ b)
    _≈_ = Pointwise A._≈_ _≡_

    open RawFunctor Pₗ.functor

    -- This type to the right of × needs to be a "lifted" version of (B : Set b)
    -- that lives in the universe (Set (a ⊔ b)).
    fmapIdₗ : (x : A.Carrier × Lift a B) → (id <$> x) ≈ x
    fmapIdₗ x = A.refl , refl

    open RawMonad   Pₗ.monad

    -- Now, let's show that "return" is a unit for >>=. We use Lift in exactly
    -- the same way as above. The data (x : B) then needs to be "lifted" to
    -- this new type (Lift B).
    returnUnitL : ∀ {x : B} {f : Lift a B → A.Carrier × Lift a B}
                  → ((return (lift x)) >>= f) ≈ f (lift x)
    returnUnitL = A.identityˡ _ , refl

    returnUnitR : {x : A.Carrier × Lift a B} → (x >>= return) ≈ x
    returnUnitR = A.identityʳ _ , refl

    -- And another (limited version of a) monad law...
    bindCompose : ∀ {f g : Lift a B → A.Carrier × Lift a B}
                → {x : A.Carrier × Lift a B}
                → ((x >>= f) >>= g) ≈ (x >>= (λ y → (f y >>= g)))
    bindCompose = A.assoc _ _ _ , refl
