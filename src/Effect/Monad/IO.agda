------------------------------------------------------------------------
-- The Agda standard library
--
-- The IO monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

open import Level

module Effect.Monad.IO where

open import Function.Base
open import IO.Base

private
  variable
    f : Level
    A : Set f

------------------------------------------------------------------------
-- IO monad operations

record RawMonadIO
       (M : Set f → Set (suc f))
       : Set (suc f) where
  field
    liftIO : IO A → M A

------------------------------------------------------------------------
-- Reader monad specifics

monadIO : RawMonadIO {f} IO
monadIO = record { liftIO = id }
