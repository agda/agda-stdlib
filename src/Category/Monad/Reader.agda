------------------------------------------------------------------------
-- The Agda standard library
--
-- The reader monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level

module Category.Monad.Reader {r} (R : Set r) (a : Level) where

open import Function
open import Function.Identity.Categorical as Id using (Identity)
open import Category.Applicative.Indexed
open import Category.Monad.Indexed
open import Category.Monad
open import Data.Unit

------------------------------------------------------------------------
-- Indexed reader

IReaderT : ∀ {ℓ} {I : Set ℓ} → IFun I (r ⊔ a) → IFun I (r ⊔ a)
IReaderT M i j A = R → M i j A

module _ {ℓ} {I : Set ℓ} {M : IFun I (r ⊔ a)} where

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

record RawIMonadReader {ℓ} {I : Set ℓ} (M : IFun I (r ⊔ a))
                       : Set (ℓ ⊔ suc (r ⊔ a)) where
  field
    monad  : RawIMonad M
    reader : ∀ {i A} → (R → A) → M i i A
    local  : ∀ {i j A} → (R → R) → M i j A → M i j A

  open RawIMonad monad public

  ask : ∀ {i} → M i i (Lift (r ⊔ a) R)
  ask = reader lift

  asks : ∀ {i A} → (R → A) → M i i A
  asks = reader

ReaderTIMonadReader : ∀ {ℓ} {I : Set ℓ} {M : IFun I (r ⊔ a)} →
                      RawIMonad M → RawIMonadReader (IReaderT M)
ReaderTIMonadReader Mon = record
  { monad = ReaderTIMonad Mon
  ; reader = λ f r → return (f r)
  ; local = λ f m → m ∘ f
  } where open RawIMonad Mon

------------------------------------------------------------------------
-- Ordinary reader monads

RawMonadReader : (M : Set (r ⊔ a) → Set (r ⊔ a)) → Set _
RawMonadReader M = RawIMonadReader {I = ⊤} (λ _ _ → M)

module RawMonadReader {M} (Mon : RawMonadReader M) where
  open RawIMonadReader Mon public

ReaderT : (M : Set (r ⊔ a) → Set (r ⊔ a)) → Set _ → Set _
ReaderT M = IReaderT {I = ⊤} (λ _ _ → M) _ _

ReaderTMonad : ∀ {M} → RawMonad M → RawMonad (ReaderT M)
ReaderTMonad = ReaderTIMonad

ReaderTMonadReader : ∀ {M} → RawMonad M → RawMonadReader (ReaderT M)
ReaderTMonadReader = ReaderTIMonadReader

ReaderTMonadZero : ∀ {M} → RawMonadZero M → RawMonadZero (ReaderT M)
ReaderTMonadZero = ReaderTIMonadZero

ReaderTMonadPlus : ∀ {M} → RawMonadPlus M → RawMonadPlus (ReaderT M)
ReaderTMonadPlus = ReaderTIMonadPlus

Reader : Set (r ⊔ a) → Set (r ⊔ a)
Reader = ReaderT Identity

ReaderMonad : RawMonad Reader
ReaderMonad = ReaderTIMonad Id.monad

ReaderMonadReader : RawMonadReader Reader
ReaderMonadReader = ReaderTIMonadReader Id.monad
