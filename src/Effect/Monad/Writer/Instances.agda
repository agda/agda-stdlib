------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for the writer monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Monad.Writer.Instances where

open import Effect.Monad.Writer.Transformer

instance
  writerTFunctor = λ {s} {S} {f} {M} {{fun}} {{mo}} → functor {s} {S} {f} {M} {mo} fun
  writerTApplicative = λ {s} {S} {f} {M} {{mo}} {{mon}} → applicative {s} {S} {f} {M} {mo} mon
  writerTEmpty = λ {s} {S} {f} {M} {{e}} {{mo}} → empty {s} {S} {f} {M} {mo} e
  writerTChoice = λ {s} {S} {f} {M} {{ch}} {{mo}} → choice {s} {S} {f} {M} {mo} ch
  writerTApplicativeZero = λ {s} {S} {f} {M} {{mo}} {{mon}} → applicativeZero {s} {S} {f} {M} {mo} mon
  writerTAlternative = λ {s} {S} {f} {M} {{mo}} {{mpl}} → alternative {s} {S} {f} {M} {mo} mpl
  writerTMonad = λ {s} {S} {f} {M} {{mo}} {{mon}} → monad {s} {S} {f} {M} {mo} mon
  writerTMonadZero = λ {s} {S} {f} {M} {{mo}} {{mz}} → monadZero {s} {S} {f} {M} {mo} mz
  writerTMonadPlus = λ {s} {S} {f} {M} {{mo}} {{mpl}} → monadPlus {s} {S} {f} {M} {mo} mpl
  writerTMonadT = λ {s} {S} {f} {M} {{mo}} {{mon}} → monadT {s} {S} {f} {M} {mo} mon
  writerTMonadWriter = λ {s} {S} {f} {M} {{mo}} {{mon}} → monadWriter {s} {S} {f} {M} {mo} mon
  writerTLiftReaderT = λ {s} {S₁} {S₂} {f} {g} {M} {{fun}} {{mw}} → liftReaderT {s} {S₁} {S₂} {f} {g} {M} fun mw
  writerTLiftStateT = λ {s} {S₁} {S₂} {f} {g} {M} {{fun}} {{mw}} → liftStateT {s} {S₁} {S₂} {f} {g} {M} fun mw
