------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for the reader monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Monad.Reader.Instances where

open import Effect.Monad.Reader.Transformer

instance
  readerTFunctor = λ {s} {S} {f} {M} {{fun}} → functor {s} {S} {f} {M} fun
  readerTApplicative = λ {s} {S} {f} {M} {{mon}} → applicative {s} {S} {f} {M} mon
  readerTEmpty = λ {s} {S} {f} {M} {{e}} → empty {s} {S} {f} {M} e
  readerTChoice = λ {s} {S} {f} {M} {{ch}} → choice {s} {S} {f} {M} ch
  readerTApplicativeZero = λ {s} {S} {f} {M} {{mon}} → applicativeZero {s} {S} {f} {M} mon
  readerTAlternative = λ {s} {S} {f} {M} {{mpl}} → alternative {s} {S} {f} {M} mpl
  readerTMonad = λ {s} {S} {f} {M} {{mon}} → monad {s} {S} {f} {M} mon
  readerTMonadZero = λ {s} {S} {f} {M} {{mz}} → monadZero {s} {S} {f} {M} mz
  readerTMonadPlus = λ {s} {S} {f} {M} {{mpl}} → monadPlus {s} {S} {f} {M} mpl
  readerTMonadT = λ {s} {S} {f} {M} {{mon}} → monadT {s} {S} {f} {M} mon
  readerTMonadReader = λ {s} {S} {f} {M} {{mon}} → monadReader {s} {S} {f} {M} mon
  readerTLiftWriterT = λ {s} {S₁} {S₂} {f} {M} {{mo}} {{fun}} {{mr}} → liftWriterT {s} {S₁} {S₂} {f} {M} mo fun mr
  readerTLiftStateT = λ {s} {S₁} {S₂} {f} {M} {{fun}} {{mr}} → liftStateT {s} {S₁} {S₂} {f} {M} fun mr
  -- the following instance conflicts with readerTMonadReader so we don't include it
  -- readerTLiftReaderT = λ {R} {s} {S} {f} {M} {{ms}} → liftReaderT {R} {s} {S} {f} {M} ms
