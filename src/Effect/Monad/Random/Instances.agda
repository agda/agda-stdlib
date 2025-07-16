------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for the IO monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module Effect.Monad.Random.Instances where

open import IO.Base using (IO)
open import Level renaming (suc to lsuc)
open import Effect.Monad.Random

instance
  ioMonadRandChar = Char.monadRandom
  ioMonadRandRChar = Char.monadRandomR

  ioMonadRandFloat = Float.monadRandom
  ioMonadRandRFloat = Float.monadRandomR

  ioMonadRandℤ = ℤ.monadRandom
  ioMonadRandRℤ = ℤ.monadRandomR

  ioMonadRandℕ = ℕ.monadRandom
  ioMonadRandRℕ = ℕ.monadRandomR

  ioMonadRandWord64 = Word64.monadRandom
  ioMonadRandRWord64 = Word64.monadRandomR

  ioMonadRandFin = λ {n} {{nz}} → Fin.monadRandom n {{nz}}
  ioMonadRandRFin = λ {n} {{nz}} → Fin.monadRandomR n {{nz}}

  ioMonadRandBool = Bool.monadRandom
  ioMonadRandRBool = Bool.monadRandomR

  ioMonadRandList = λ {a} {A} {{rA}} → List.monadRandom {a} {A} (RawMonadRandom.getRandom {a} {lsuc a} {A} {IO} rA)

  ioMonadRandVec = λ {a} {A} {{rA}} {n} → Vec.monadRandom {a} {A} (RawMonadRandom.getRandom {a} {lsuc a} {A} {IO} rA) n

  ioMonadRandVec≤ = λ {a} {A} {{rA}} {n} → Vec≤.monadRandom {a} {A} (RawMonadRandom.getRandom {a} {lsuc a} {A} {IO} rA) n

  ioMonadRandString = String.monadRandom

  ioMonadRandString≤ = λ {n} → String≤.monadRandom n

  ioMonadRandRangedString≤ = λ {a} {b} .{a≤b} {n} → RangedString≤.monadRandom a b a≤b n


  stateTMonadRand = λ {a} {s} {A} {S} {M} {{m}} {{mrand}} → liftStateT {a} {s} {A} {S} {M} m mrand
  stateTMonadRandR = λ {a} {s} {A} {R} {S} {M} {{m}} {{mrand}} → liftRStateT {a} {s} {A} {R} {S} {M} m mrand

  readerTMonadRand = λ {a} {b} {A} {B} {M} {{mrand}} → liftReaderT {a} {b} {A} {B} {M} mrand
  readerTMonadRandR = λ {a} {b} {A} {R} {B} {M} {{mrand}} → liftRReaderT {a} {b} {A} {R} {B} {M} mrand

  writerTMonadRand = λ {a} {f} {w} {A} {W} {M} {{m}} {{mrand}} → liftWriterT {a} {f} {w} {A} {W} {M} m mrand
  writerTMonadRandR = λ {a} {f} {w} {A} {R} {W} {M} {{m}} {{mrand}} → liftRWriterT {a} {f} {w} {A} {R} {W} {M} m mrand
