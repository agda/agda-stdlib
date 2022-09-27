------------------------------------------------------------------------
-- The Agda standard library
--
-- Monads
------------------------------------------------------------------------

-- Note that currently the monad laws are not included here.

{-# OPTIONS --without-K --safe #-}

module Effect.Monad where

open import Effect.Applicative
open import Function.Base using (flip; _$′_)
open import Level using (Level; suc)

private
  variable
    f : Level
    A B C : Set f

------------------------------------------------------------------------
-- The type of raw monads

record RawMonad (F : Set f → Set f) : Set (suc f) where
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

  Kleisli : Set f → Set f → Set f
  Kleisli A B = A → F B

  _>=>_ : Kleisli A B → Kleisli B C → Kleisli A C
  (f >=> g) a = f a >>= g

  _<=<_ : Kleisli B C → Kleisli A B → Kleisli A C
  _<=<_ = flip _>=>_

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
    mkRawApplicative pure $′ λ mf mx → do
      f ← mf
      x ← mx
      pure (f x)
  mkRawMonad F pure _>>=_ ._>>=_ = _>>=_

------------------------------------------------------------------------
-- The type of raw monads with a zero

record RawMonadZero (F : Set f → Set f) : Set (suc f) where
  field
    rawMonad : RawMonad F
    empty : F A

  open RawMonad rawMonad public

  rawApplicativeZero : RawApplicativeZero F
  rawApplicativeZero = record
    { rawApplicative = rawApplicative
    ; empty = empty
    }

------------------------------------------------------------------------
-- The type of raw monadplus

------------------------------------------------------------------------
-- The type of raw monad transformer

-- F has been RawMonadT'd as TF
record RawMonadTd (F TF : Set f → Set f) : Set (suc f) where
  field
    lift : F A → TF A
    rawMonad : RawMonad TF

RawMonadT : (T : (Set f → Set f) → (Set f → Set f)) → Set (suc f)
RawMonadT T = ∀ {M} → RawMonad M → RawMonadTd M (T M)
