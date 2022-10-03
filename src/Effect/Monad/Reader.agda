------------------------------------------------------------------------
-- The Agda standard library
--
-- The reader monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level

module Effect.Monad.Reader {r} (R : Set r) (a : Level) where

open import Effect.Monad
open import Function.Base
open import Function.Identity.Effectful as Id using (Identity)

private
  variable
    ℓ : Level
    A B I : Set ℓ

------------------------------------------------------------------------
-- Reader

record RawMonadReader (M : Set (r ⊔ a) → Set (r ⊔ a)) : Set (suc (r ⊔ a)) where
  field
    rawMonad : RawMonad M
    reader : (R → A) → M A
    local  : (R → R) → M A → M A

  ask : M (Lift a R)
  ask = reader lift

------------------------------------------------------------------------
-- Reader transformer

record ReaderT
       (M : Set (r ⊔ a) → Set (r ⊔ a))
       (A : Set (r ⊔ a))
       : Set (r ⊔ a) where
  constructor mkReaderT
  field runReaderT : R → M A

rawMonadT : RawMonadT ReaderT
rawMonadT M = record
  { lift = mkReaderT ∘′ const
  ; rawMonad = mkRawMonad _
                 (mkReaderT ∘′ const ∘′ pure)
                 λ ma f → mkReaderT $ λ r →
                    do a ← ReaderT.runReaderT ma r
                       b ← ReaderT.runReaderT (f a) r
                       pure b
  } where open RawMonad M

rawMonadReaderT : ∀ {M} → RawMonad M → RawMonadReader (ReaderT M)
rawMonadReaderT M = record
  { rawMonad = RawMonadTd.rawMonad (rawMonadT M)
  ; reader = λ f → mkReaderT (pure ∘′ f)
  ; local = λ f ma → mkReaderT (ReaderT.runReaderT ma ∘′ f)
  } where open RawMonad M

rawMonadZeroT : ∀ {M} → RawMonadZero M → RawMonadZero (ReaderT M)
rawMonadZeroT M = record
  { rawMonad = RawMonadTd.rawMonad (rawMonadT rawMonad)
  ; rawEmpty = record { empty = mkReaderT (const empty) }
  } where open RawMonadZero M

rawMonadPlusT : ∀ {M} → RawMonadPlus M → RawMonadPlus (ReaderT M)
rawMonadPlusT M = record
  { rawMonadZero = rawMonadZeroT rawMonadZero
  ; rawChoice = record { _<|>_ = λ ma₁ ma₂ → mkReaderT $ λ r →
                                 ReaderT.runReaderT ma₁ r
                                 <|> ReaderT.runReaderT ma₂ r
                       }
  } where open RawMonadPlus M

------------------------------------------------------------------------
-- Ordinary reader monad

Reader : Set (r ⊔ a) → Set (r ⊔ a)
Reader = ReaderT Identity

rawMonad : RawMonad Reader
rawMonad = RawMonadTd.rawMonad (rawMonadT Id.monad)

rawMonadReader : RawMonadReader Reader
rawMonadReader = rawMonadReaderT Id.monad
