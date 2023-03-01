------------------------------------------------------------------------
-- The Agda standard library
--
-- The indexed reader monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level

module Effect.Monad.Reader.Indexed {r} (R : Set r) (a : Level) where

open import Function
open import Function.Identity.Effectful as Id using (Identity)
open import Effect.Applicative.Indexed
open import Effect.Monad.Indexed
open import Effect.Monad
open import Data.Unit

private
  variable
    ℓ : Level
    A B I : Set ℓ

------------------------------------------------------------------------
-- Indexed reader

IReaderT : IFun I (r ⊔ a) → IFun I (r ⊔ a)
IReaderT M i j A = R → M i j A

module _ {M : IFun I (r ⊔ a)} where

  ------------------------------------------------------------------------
  -- Indexed reader applicative

  ReaderTIApplicative : RawIApplicative M → RawIApplicative (IReaderT M)
  ReaderTIApplicative App = record
    { pure = λ x r → pure x
    ; _⊛_ = λ m n r → m r ⊛ n r
    } where open RawIApplicative App

  ReaderTIApplicativeZero : RawIApplicativeZero M →
                            RawIApplicativeZero (IReaderT M)
  ReaderTIApplicativeZero App = record
    { applicative = ReaderTIApplicative applicative
    ; ∅ = const ∅
    } where open RawIApplicativeZero App

  ReaderTIAlternative : RawIAlternative M → RawIAlternative (IReaderT M)
  ReaderTIAlternative Alt = record
    { applicativeZero = ReaderTIApplicativeZero applicativeZero
    ; _∣_ = λ m n r → m r ∣ n r
    } where open RawIAlternative Alt

  ------------------------------------------------------------------------
  -- Indexed reader monad

  ReaderTIMonad : RawIMonad M → RawIMonad (IReaderT M)
  ReaderTIMonad Mon = record
    { return = λ x r → return x
    ; _>>=_ = λ m f r → m r >>= flip f r
    } where open RawIMonad Mon

  ReaderTIMonadZero : RawIMonadZero M → RawIMonadZero (IReaderT M)
  ReaderTIMonadZero Mon = record
    { monad = ReaderTIMonad monad
    ; applicativeZero = ReaderTIApplicativeZero applicativeZero
    } where open RawIMonadZero Mon

  ReaderTIMonadPlus : RawIMonadPlus M → RawIMonadPlus (IReaderT M)
  ReaderTIMonadPlus Mon = record
    { monad = ReaderTIMonad monad
    ; alternative = ReaderTIAlternative alternative
    } where open RawIMonadPlus Mon

------------------------------------------------------------------------
-- Reader monad operations

record RawIMonadReader {I : Set ℓ} (M : IFun I (r ⊔ a))
                       : Set (ℓ ⊔ suc (r ⊔ a)) where
  field
    monad  : RawIMonad M
    reader : ∀ {i} → (R → A) → M i i A
    local  : ∀ {i j} → (R → R) → M i j A → M i j A

  open RawIMonad monad public

  ask : ∀ {i} → M i i (Lift (r ⊔ a) R)
  ask = reader lift

  asks : ∀ {i} → (R → A) → M i i A
  asks = reader

ReaderTIMonadReader : {I : Set ℓ} {M : IFun I (r ⊔ a)} →
                      RawIMonad M → RawIMonadReader (IReaderT M)
ReaderTIMonadReader Mon = record
  { monad = ReaderTIMonad Mon
  ; reader = λ f r → return (f r)
  ; local = λ f m → m ∘ f
  } where open RawIMonad Mon
