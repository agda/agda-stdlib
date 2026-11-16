------------------------------------------------------------------------
-- The Agda standard library
--
-- The writer monad transformer
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


module Effect.Monad.Writer.Transformer where

open import Algebra using (RawMonoid)
open import Data.Product.Base using (_×_; _,_; proj₂; map₂)
open import Effect.Applicative using (RawApplicative; RawApplicativeZero; RawAlternative)
open import Effect.Choice using (RawChoice)
open import Effect.Empty using (RawEmpty)
open import Effect.Functor using (RawFunctor)
open import Effect.Monad using (RawMonad; RawMonadZero; RawMonadPlus; RawMonadT)
open import Function.Base using (_∘′_; const; _$_)
open import Level using (Level)

private
  variable
    w g g₁ g₂ : Level
    A B : Set w
    M : Set w → Set g
    𝕎 : RawMonoid w g

------------------------------------------------------------------------
-- Re-export the basic type definitions

open import Effect.Monad.Writer.Transformer.Base public
  using ( RawMonadWriter
        ; WriterT
        ; mkWriterT
        ; runWriterT
        )

------------------------------------------------------------------------
-- Structure

functor : RawFunctor M → RawFunctor (WriterT 𝕎 M)
functor M = record
  { _<$>_ = λ f ma → mkWriterT λ w → map₂ f <$> runWriterT ma w
  } where open RawFunctor M

empty : RawEmpty M → RawEmpty (WriterT 𝕎 M)
empty M = record
  { empty = mkWriterT (const (RawEmpty.empty M))
  }

choice : RawChoice M → RawChoice (WriterT 𝕎 M)
choice M = record
  { _<|>_ = λ ma₁ ma₂ → mkWriterT λ w →
            WriterT.runWriterT ma₁ w
            <|> WriterT.runWriterT ma₂ w
  } where open RawChoice M

module _ {𝕎 : RawMonoid w g} where

  open RawMonoid 𝕎 renaming (Carrier to W)

  applicative : RawApplicative M → RawApplicative (WriterT 𝕎 M)
  applicative M = record
    { rawFunctor = functor rawFunctor
    ; pure = λ a → mkWriterT (pure ∘′ (_, a))
    ; _<*>_ = λ mf mx → mkWriterT $ λ w →
              (go <$> runWriterT mf w) <*> runWriterT mx ε
    } where
        open RawApplicative M
        go : W × (A → B) → W × A → W × B
        go (w₁ , f) (w₂ , x) = w₁ ∙ w₂ , f x

  applicativeZero : RawApplicativeZero M → RawApplicativeZero (WriterT 𝕎 M)
  applicativeZero M = record
    { rawApplicative = applicative rawApplicative
    ; rawEmpty = empty rawEmpty
    } where open RawApplicativeZero M using (rawApplicative; rawEmpty)

  alternative : RawAlternative M → RawAlternative (WriterT 𝕎 M)
  alternative M = record
    { rawApplicativeZero = applicativeZero rawApplicativeZero
    ; rawChoice = choice rawChoice
    } where open RawAlternative M

  monad : RawMonad M → RawMonad (WriterT 𝕎 M)
  monad M = record
    { rawApplicative = applicative rawApplicative
    ; _>>=_ = λ ma f → mkWriterT λ w → do
        w₁ , a  ← runWriterT ma w
        runWriterT (f a) w₁
    } where open RawMonad M

  monadZero : RawMonadZero M → RawMonadZero (WriterT 𝕎 M)
  monadZero M = record
    { rawMonad = monad (RawMonadZero.rawMonad M)
    ; rawEmpty = empty (RawMonadZero.rawEmpty M)
    }

  monadPlus : RawMonadPlus M → RawMonadPlus (WriterT 𝕎 M)
  monadPlus M = record
    { rawMonadZero = monadZero rawMonadZero
    ; rawChoice = choice rawChoice
    } where open RawMonadPlus M

  ----------------------------------------------------------------------
  -- Monad writer transformer specifics

  monadT : RawMonadT {g₁ = g₁} {g₂ = _} (WriterT 𝕎)
  monadT M = record
    { lift = mkWriterT ∘′ λ ma w → (w ,_) <$> ma
    ; rawMonad = monad M
    } where open RawMonad M

  monadWriter : RawMonad M → RawMonadWriter 𝕎 (WriterT 𝕎 M)
  monadWriter M = record
    { writer = mkWriterT ∘′ λ (w' , a) w → pure (w ∙ w' , a)
    ; listen = λ ma → mkWriterT λ w → do
             w , a ← runWriterT ma w
             pure (w , w , a)
    ; pass = λ mx → mkWriterT λ w → do
           w , f , a ← runWriterT mx w
           pure (f w , a)
    } where open RawMonad M

module _ {𝕎₁ : RawMonoid w g₁} where

  open RawMonoid 𝕎₁ renaming (Carrier to W₁)

  liftWriterT : (𝕎₂ : RawMonoid w g₂) →
                RawFunctor M →
                RawMonadWriter 𝕎₁ M →
                RawMonadWriter 𝕎₁ (WriterT 𝕎₂ M)
  liftWriterT 𝕎₂ M MWrite = record
    { writer = λ (w , a) → mkWriterT λ w' → (writer (w , w' , a ))
    ; listen = λ mx → mkWriterT λ w' → ((λ (w₁ , w₂ , a) → w₂ , w₁ , a) <$> listen (runWriterT mx w'))
    ; pass = λ mx → mkWriterT λ w' → (pass ((λ (w , f , a) → f , w , a) <$> runWriterT mx w'))
    } where open RawMonadWriter MWrite
            open RawFunctor M

  private
    variable
      W₂ : Set g₂

  open import Effect.Monad.Reader.Transformer.Base

  liftReaderT : RawFunctor M →
                RawMonadWriter 𝕎₁ M →
                RawMonadWriter 𝕎₁ (ReaderT W₂ M)
  liftReaderT M MWrite = record
    { writer = mkReaderT ∘′ const ∘′ writer
    ; listen = λ ma → mkReaderT (listen ∘′ runReaderT ma)
    ; pass = λ ma → mkReaderT (pass ∘′ runReaderT ma)
    } where open RawMonadWriter MWrite

  open import Effect.Monad.State.Transformer.Base

  liftStateT : RawFunctor M →
               RawMonadWriter 𝕎₁ M →
               RawMonadWriter 𝕎₁ (StateT W₂ M)
  liftStateT M MWrite = record
    { writer = λ x → mkStateT λ w₂ → (w₂ ,_) <$>
                 writer x
    ; listen = λ mx → mkStateT λ w₂ → (w₂ ,_) <$>
                 listen (proj₂ <$> runStateT mx w₂)
    ; pass = λ mx → mkStateT λ w₂ → (w₂ ,_) <$>
               pass ((λ (_ , f , a) → f , a) <$> runStateT mx w₂)
    } where open RawMonadWriter MWrite
            open RawFunctor M
