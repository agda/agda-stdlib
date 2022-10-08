------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for the IO monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module Effect.Monad.IO.Instances where

open import Effect.Monad.IO

instance
  ioMonadIO = monadIO
  stateTMonadIO = λ {s} {S} {M} {{m}} {{mio}} → monadIOStateT {s} {S} {M} m mio
  readerTMonadIO = λ {r} {R} {a} {M} {{mio}} → monadIOReaderT  {r} {R} {a} {M} mio
