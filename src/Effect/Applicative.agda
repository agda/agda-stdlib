------------------------------------------------------------------------
-- The Agda standard library
--
-- Applicative functors
------------------------------------------------------------------------

-- Note that currently the applicative functor laws are not included
-- here.

{-# OPTIONS --without-K --safe #-}

module Effect.Applicative where

open import Data.Product using (_×_; _,_)
open import Effect.Choice using (RawChoice)
open import Effect.Empty using (RawEmpty)
open import Effect.Functor using (RawFunctor)
open import Function.Base using (const; flip; _∘′_)
open import Level using (Level; suc; _⊔_)

private
  variable
    f : Level
    A B : Set f
------------------------------------------------------------------------
-- The type of raw applicatives

record RawApplicative (F : Set f → Set f) : Set (suc f) where
  infixl 4 _<*>_ _<*_ _*>_
  infixl 4 _⊛_ _<⊛_ _⊛>_
  infix  4 _⊗_
  field
    rawFunctor : RawFunctor F
    pure : A → F A
    _<*>_ : F (A → B) → F A → F B

  open RawFunctor rawFunctor public

  _<*_ : F A → F B → F A
  a <* b = const <$> a <*> b

  _*>_ : F A → F B → F B
  a *> b = flip const <$> a <*> b

  -- backwards compatibility: unicode variants
  _⊛_ : F (A → B) → F A → F B
  _⊛_ = _<*>_

  _<⊛_ : F A → F B → F A
  _<⊛_ = _<*_

  _⊛>_ : F A → F B → F B
  _⊛>_ = _*>_

  _⊗_ : F A → F B → F (A × B)
  fa ⊗ fb = _,_ <$> fa <*> fb

module _ where

  open RawApplicative
  open RawFunctor

  -- Smart constructor
  mkRawApplicative :
    {F : Set f → Set f} →
    (pure : ∀ {A} → A → F A) →
    (app : ∀ {A B} → F (A → B) → F A → F B) →
    RawApplicative F
  mkRawApplicative pure app .rawFunctor ._<$>_ = app ∘′ pure
  mkRawApplicative pure app .pure = pure
  mkRawApplicative pure app ._<*>_ = app

------------------------------------------------------------------------
-- The type of raw applicatives with a zero

record RawApplicativeZero (F : Set f → Set f) : Set (suc f) where
  field
    rawApplicative : RawApplicative F
    rawEmpty : RawEmpty F

  open RawApplicative rawApplicative public

------------------------------------------------------------------------
-- The type of raw alternative applicatives

record RawAlternative (F : Set f → Set f) : Set (suc f) where
  field
    rawApplicativeZero : RawApplicativeZero F
    rawChoice : RawChoice F

  open RawApplicativeZero rawApplicativeZero public
