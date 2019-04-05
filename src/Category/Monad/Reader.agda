------------------------------------------------------------------------
-- The Agda standard library
--
-- The reader monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Category.Monad.Reader where

open import Level
open import Function
open import Function.Identity.Categorical as Id using (Identity)
open import Category.Applicative.Indexed
open import Category.Monad.Indexed
open import Category.Monad
open import Data.Unit

------------------------------------------------------------------------
-- Indexed reader

IReaderT : ∀ {r} (R : Set r) {i} {I : Set i} (M : IFun I r) → IFun I r
IReaderT R M i j A = R → M i j A

------------------------------------------------------------------------
-- Indexed reader applicative

ReaderTIApplicative : ∀ {r} (R : Set r) {i} {I : Set i} {M : IFun I r} →
                      RawIApplicative M → RawIApplicative (IReaderT R M)
ReaderTIApplicative R App = record
  { pure = λ x r → pure x
  ; _⊛_ = λ m n r → m r ⊛ n r
  } where open RawIApplicative App

ReaderTIApplicativeZero : ∀ {r} (R : Set r) {i} {I : Set i} {M : IFun I r} →
                          RawIApplicativeZero M →
                          RawIApplicativeZero (IReaderT R M)
ReaderTIApplicativeZero R App = record
  { applicative = ReaderTIApplicative R applicative
  ; ∅ = const ∅
  } where open RawIApplicativeZero App

ReaderTIAlternative : ∀ {r} (R : Set r) {i} {I : Set i} {M : IFun I r} →
                      RawIAlternative M →
                      RawIAlternative (IReaderT R M)
ReaderTIAlternative R Alt = record
  { applicativeZero = ReaderTIApplicativeZero R applicativeZero
  ; _∣_ = λ m n r → m r ∣ n r
  } where open RawIAlternative Alt

------------------------------------------------------------------------
-- Indexed reader monad

ReaderTIMonad : ∀ {r} (R : Set r) {i} {I : Set i} {M : IFun I r} →
                RawIMonad M → RawIMonad (IReaderT R M)
ReaderTIMonad R Mon = record
  { return = λ x r → return x
  ; _>>=_ = λ m f r → m r >>= flip f r
  } where open RawIMonad Mon

ReaderTIMonadZero : ∀ {r} (R : Set r) {i} {I : Set i} {M : IFun I r} →
                    RawIMonadZero M → RawIMonadZero (IReaderT R M)
ReaderTIMonadZero R Mon = record
  { monad = ReaderTIMonad R monad
  ; applicativeZero = ReaderTIApplicativeZero R applicativeZero
  } where open RawIMonadZero Mon

ReaderTIMonadPlus : ∀ {r} (R : Set r) {i} {I : Set i} {M : IFun I r} →
                    RawIMonadPlus M → RawIMonadPlus (IReaderT R M)
ReaderTIMonadPlus R Mon = record
  { monad = ReaderTIMonad R monad
  ; alternative = ReaderTIAlternative R alternative
  } where open RawIMonadPlus Mon

------------------------------------------------------------------------
-- Reader monad operations

record RawIMonadReader {r} (R : Set r) {i} {I : Set i}
                       (M : IFun I r) : Set (i ⊔ suc r) where
  field
    monad : RawIMonad M
    ask   : ∀ {i} → M i i R
    local : ∀ {i j} → (R → R) → M i j R → M i j R

  open RawIMonad monad public

  asks : ∀ {i A} → (R → A) → M i i A
  asks f = f <$> ask

ReaderTIMonadReader : ∀ {r} (R : Set r) {i} {I : Set i} {M : IFun I r} →
                      RawIMonad M → RawIMonadReader R (IReaderT R M)
ReaderTIMonadReader R Mon = record
  { monad = ReaderTIMonad R Mon
  ; ask = return
  ; local = λ f m → m ∘ f
  } where open RawIMonad Mon

------------------------------------------------------------------------
-- Ordinary reader monads

RawMonadReader : ∀ {r} → Set r → (Set r → Set r) → Set _
RawMonadReader R M = RawIMonadReader R {I = ⊤} (λ _ _ → M)

module RawMonadReader {r} {R : Set r} {M : Set r → Set r}
                      (Mon : RawMonadReader R M) where
  open RawIMonadReader Mon public

ReaderT : ∀ {r} (R : Set r) (M : Set r → Set r) → Set r → Set r
ReaderT R M = IReaderT R {I = ⊤} (λ _ _ → M) _ _

ReaderTMonad : ∀ {r} (R : Set r) {M} → RawMonad M → RawMonad (ReaderT R M)
ReaderTMonad R Mon = ReaderTIMonad R Mon

ReaderTMonadReader : ∀ {r} (R : Set r) {M} →
                     RawMonad M → RawMonadReader R (ReaderT R M)
ReaderTMonadReader R Mon = ReaderTIMonadReader R Mon

ReaderTMonadZero : ∀ {r} (R : Set r) {M} →
                   RawMonadZero M → RawMonadZero (ReaderT R M)
ReaderTMonadZero R Mon = ReaderTIMonadZero R Mon

ReaderTMonadPlus : ∀ {r} (R : Set r) {M} →
                   RawMonadPlus M → RawMonadPlus (ReaderT R M)
ReaderTMonadPlus R Mon = ReaderTIMonadPlus R Mon

Reader : ∀ {r} → Set r → Set r → Set r
Reader R = ReaderT R Identity

ReaderMonad : ∀ {r} (R : Set r) → RawMonad (Reader R)
ReaderMonad R = ReaderTIMonad R Id.monad

ReaderMonadReader : ∀ {r} (R : Set r) → RawMonadReader R (Reader R)
ReaderMonadReader R = ReaderTIMonadReader R Id.monad
