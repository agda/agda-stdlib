------------------------------------------------------------------------
-- The Agda standard library
--
-- Monads
------------------------------------------------------------------------

-- Note that currently the monad laws are not included here.

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Monad where

open import Data.Bool.Base using (Bool; true; false; not)
open import Data.Unit.Polymorphic.Base using (⊤)

open import Effect.Choice
open import Effect.Empty
open import Effect.Applicative
open import Function.Base using (flip; _$′_; _∘′_)
open import Level using (Level; suc; _⊔_)

private
  variable
    f g g₁ g₂ : Level
    A B C : Set f

------------------------------------------------------------------------
-- The type of raw monads

record RawMonad (F : Set f → Set g) : Set (suc f ⊔ g) where
  infixl 1 _>>=_ _>>_ _>=>_
  infixr 1 _=<<_ _<=<_
  field
    rawApplicative : RawApplicative F
    _>>=_ : F A → (A → F B) → F B

  open RawApplicative rawApplicative public

  _>>_ : F A → F B → F B
  _>>_ = _*>_

  _=<<_ : (A → F B) → F A → F B
  _=<<_ = flip _>>=_

  Kleisli : Set f → Set f → Set (f ⊔ g)
  Kleisli A B = A → F B

  _>=>_ : Kleisli A B → Kleisli B C → Kleisli A C
  (f >=> g) a = f a >>= g

  _<=<_ : Kleisli B C → Kleisli A B → Kleisli A C
  _<=<_ = flip _>=>_

  when : Bool → F ⊤ → F ⊤
  when true m = m
  when false m = pure _

  unless : Bool → F ⊤ → F ⊤
  unless = when ∘′ not

-- Smart constructor
module _ where

  open RawMonad
  open RawApplicative

  mkRawMonad :
    (F : Set f → Set f) →
    (pure : ∀ {A} → A → F A) →
    (bind : ∀ {A B} → F A → (A → F B) → F B) →
    RawMonad F
  mkRawMonad F pure _>>=_ .rawApplicative =
    mkRawApplicative _ pure $′ λ mf mx → do
      f ← mf
      x ← mx
      pure (f x)
  mkRawMonad F pure _>>=_ ._>>=_ = _>>=_

------------------------------------------------------------------------
-- The type of raw monads with a zero

record RawMonadZero (F : Set f → Set g) : Set (suc f ⊔ g) where
  field
    rawMonad : RawMonad F
    rawEmpty : RawEmpty F

  open RawMonad rawMonad public
  open RawEmpty rawEmpty public

  rawApplicativeZero : RawApplicativeZero F
  rawApplicativeZero = record
    { rawApplicative = rawApplicative
    ; rawEmpty = rawEmpty
    }

------------------------------------------------------------------------
-- The type of raw monadplus

record RawMonadPlus (F : Set f → Set g) : Set (suc f ⊔ g) where
  field
    rawMonadZero : RawMonadZero F
    rawChoice    : RawChoice F

  open RawMonadZero rawMonadZero public
  open RawChoice rawChoice public

  rawAlternative : RawAlternative F
  rawAlternative = record
    { rawApplicativeZero = rawApplicativeZero
    ; rawChoice = rawChoice
    }

------------------------------------------------------------------------
-- The type of raw monad transformer

-- F has been RawMonadT'd as TF
record RawMonadTd (F : Set f → Set g₁) (TF : Set f → Set g₂) : Set (suc f ⊔ g₁ ⊔ g₂) where
  field
    lift : F A → TF A
    rawMonad : RawMonad TF

  open RawMonad rawMonad public

RawMonadT : (T : (Set f → Set g₁) → (Set f → Set g₂)) → Set (suc f ⊔ suc g₁ ⊔ g₂)
RawMonadT T = ∀ {M} → RawMonad M → RawMonadTd M (T M)
