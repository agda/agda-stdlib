------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for the IO monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module Effect.Monad.IO.Instances where

open import Effect.Monad.IO

instance
  ioMonadIO = monadIO
  stateTMonadIO = λ {s} {S} {M} {{m}} {{mio}} → liftStateT {s} {S} {M} m mio
  readerTMonadIO = λ {r} {R} {M} {{mio}} → liftReaderT  {r} {R} {M} mio
  writerTMonadIO = λ {f} {w} {W} {M} {{m}} {{mio}} → liftWriterT {f} {w} {W} {M} m mio
