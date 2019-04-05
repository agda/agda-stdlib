------------------------------------------------------------------------
-- The Agda standard library
--
-- The reader monad
------------------------------------------------------------------------

module Category.Monad.Reader where

open import Level
open import Function
open import Function.Identity.Categorical as Id using (Identity)
open import Category.Applicative.Indexed using (IFun)
open import Category.Monad.Indexed
open import Category.Monad
open import Data.Unit

------------------------------------------------------------------------
-- Indexed reader

IReaderT : ∀ {r} (R : Set r) {i} {I : Set i} (M : IFun I r) → IFun I r
IReaderT R M i j A = R → M i j A

------------------------------------------------------------------------
-- Indexed reader monad

ReaderTIMonad : ∀ {r} (R : Set r) {i} {I : Set i} {M : IFun I r} →
                RawIMonad M → RawIMonad (IReaderT R M)
ReaderTIMonad R Mon = record
  { return = λ x r → return x
  ; _>>=_ = λ m f r → m r >>= flip f r
  } where open RawIMonad Mon

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
-- Ordinary reader monad

ReaderT : ∀ {r} (R : Set r) (M : Set r → Set r) → Set r → Set r
ReaderT R M = IReaderT R {I = ⊤} (λ _ _ → M) _ _

RawMonadReader : ∀ {r} → Set r → (Set r → Set r) → Set _
RawMonadReader R M = RawIMonadReader R {I = ⊤} (λ _ _ → M)

module RawMonadReader {r} {R : Set r} {M : Set r → Set r}
                      (Mon : RawMonadReader R M) where
  open RawIMonadReader Mon public

Reader : ∀ {r} → Set r → Set r → Set r
Reader R = ReaderT R Identity

ReaderMonad : ∀ {r} (R : Set r) → RawMonad (Reader R)
ReaderMonad R = ReaderTIMonad R Id.monad

ReaderMonadReader : ∀ {r} (R : Set r) → RawMonadReader R (Reader R)
ReaderMonadReader R = ReaderTIMonadReader R Id.monad
