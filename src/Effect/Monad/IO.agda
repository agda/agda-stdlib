------------------------------------------------------------------------
-- The Agda standard library
--
-- The IO monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

open import Level

module Effect.Monad.IO where

open import Data.Product using (_,_)
open import Function.Base
open import IO.Base using (IO)
open import Effect.Functor
open import Effect.Monad

private
  variable
    f g : Level
    A : Set f
    M : Set f → Set g

------------------------------------------------------------------------
-- IO monad operations

record RawMonadIO
       (M : Set f → Set (suc f))
       : Set (suc f) where
  field
    liftIO : IO A → M A

------------------------------------------------------------------------
-- IO monad specifics

monadIO : RawMonadIO {f} IO
monadIO = record { liftIO = id }

open import Effect.Monad.State.Transformer.Base using (StateT; mkStateT)

liftStateT : ∀ {S} → RawFunctor M → RawMonadIO M → RawMonadIO (StateT S M)
liftStateT M MIO = record
  { liftIO = λ io → mkStateT (λ s → (s ,_) <$> liftIO io)
  } where open RawFunctor M; open RawMonadIO MIO

open import Effect.Monad.Reader.Transformer.Base using (ReaderT; mkReaderT)

liftReaderT : ∀ {R} → RawMonadIO M → RawMonadIO (ReaderT R M)
liftReaderT MIO = record
  { liftIO = λ io → mkReaderT (λ r → liftIO io)
  } where open RawMonadIO MIO

open import Effect.Monad.Writer.Transformer.Base using (WriterT; mkWriterT)

liftWriterT : ∀ {f 𝕎} → RawFunctor M → RawMonadIO M → RawMonadIO (WriterT {f = f} 𝕎 M)
liftWriterT M MIO = record
  { liftIO = λ io → mkWriterT (λ w → (w ,_) <$> liftIO io)
  } where open RawFunctor M; open RawMonadIO MIO
