------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for the state monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Monad.State.Instances where

open import Effect.Monad.State.Transformer

instance
  stateTFunctor = λ {s} {S} {f} {M} {{fun}} → functor {s} {S} {f} {M} fun
  stateTApplicative = λ {s} {S} {f} {M} {{mon}} → applicative {s} {S} {f} {M} mon
  stateTEmpty = λ {s} {S} {f} {M} {{e}} → empty {s} {S} {f} {M} e
  stateTChoice = λ {s} {S} {f} {M} {{ch}} → choice {s} {S} {f} {M} ch
  stateTApplicativeZero = λ {s} {S} {f} {M} {{mon}} → applicativeZero {s} {S} {f} {M} mon
  stateTAlternative = λ {s} {S} {f} {M} {{mpl}} → alternative {s} {S} {f} {M} mpl
  stateTMonad = λ {s} {S} {f} {M} {{mon}} → monad {s} {S} {f} {M} mon
  stateTMonadZero = λ {s} {S} {f} {M} {{mz}} → monadZero {s} {S} {f} {M} mz
  stateTMonadPlus = λ {s} {S} {f} {M} {{mpl}} → monadPlus {s} {S} {f} {M} mpl
  stateTMonadT = λ {s} {S} {f} {M} {{mon}} → monadT {s} {S} {f} {M} mon
  stateTMonadState = λ {s} {S} {f} {M} {{mon}} → monadState {s} {S} {f} {M} mon
  stateTLiftReaderT = λ {R} {s} {S} {f} {M} {{ms}} → liftReaderT {R} {s} {S} {f} {M} ms
  stateTLiftWriterT = λ {R} {s} {S} {f} {M} {{fun}} {{mo}} {{ms}} → liftWriterT {R} {s} {S} {f} {M} mo fun ms
  -- the following instances conflicts with stateTMonadState so we don't include it
  -- stateTLiftStateT = λ {s} {S₁} {S₂} {f} {M} {{mon}} {{ms}} → liftStateT {s} {S₁} {S₂} {f} {M} mon ms
