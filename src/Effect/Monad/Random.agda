------------------------------------------------------------------------
-- The Agda standard library
--
-- The Random monad class
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module Effect.Monad.Random where

open import Algebra using (RawMonoid)
open import Effect.Functor using (RawFunctor)
open import Function.Base using (id; const)
open import IO.Base using (IO)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel)

open import System.Random as Random using (RandomRIO; InBounds)

private
  variable
    e f g s w : Level
    A : Set f
    B : Set g
    E : Set e
    S : Set s
    R : Rel A f
    M : Set f → Set g

------------------------------------------------------------------------
-- Random monad operations

record RawMonadRandom
       (A : Set f)
       (M : Set f → Set g)
       : Set (f ⊔ g) where
  field
    getRandom : M A

record RawMonadRandomR
       (A : Set f) (_≤_ : Rel A f)
       (M : Set f → Set g)
       : Set (f ⊔ g) where
  field
    getRandom  : M A
    getRandomR : (lo hi : A) → .(lo≤hi : lo ≤ hi) → M (InBounds _≤_ lo hi)

------------------------------------------------------------------------
-- Operations over RawMonadRandom

forgetRanged : RawMonadRandomR A R M → RawMonadRandom A M
forgetRanged m = record { getRandom = RawMonadRandomR.getRandom m }

------------------------------------------------------------------------
-- IO monad specifics

module MkRandomIOInstances
  {a} {A : Set a} (_≤_ : Rel A a)
  (randomIO : IO A)
  (randomRIO : RandomRIO _≤_) where

  monadRandomR : RawMonadRandomR A _≤_ IO
  monadRandomR = record
    { getRandom = randomIO
    ; getRandomR = randomRIO }

  monadRandom : RawMonadRandom A IO
  monadRandom = forgetRanged monadRandomR

module Char where

  open import Data.Char.Base using (Char; _≤_)
  open MkRandomIOInstances _≤_ Random.Char.randomIO Random.Char.randomRIO public

module Float where

  open import Data.Float.Base using (Float; _≤_)
  open MkRandomIOInstances _≤_ Random.Float.randomIO Random.Float.randomRIO public

module ℤ where

  open import Data.Integer.Base using (ℤ; _≤_)
  open MkRandomIOInstances _≤_ Random.ℤ.randomIO Random.ℤ.randomRIO public

module ℕ where

  open import Data.Nat.Base using (ℕ; _≤_)
  open MkRandomIOInstances _≤_ Random.ℕ.randomIO Random.ℕ.randomRIO public

module Word64 where

  open import Data.Word64.Base using (Word64; _≤_)
  open MkRandomIOInstances _≤_ Random.Word64.randomIO Random.Word64.randomRIO public

module Fin where

  open import Data.Nat.Base using (ℕ; NonZero)
  open import Data.Fin.Base using (Fin; _≤_)

  module _ (n : ℕ) .{{p : NonZero n}} where
    open MkRandomIOInstances _≤_ (Random.Fin.randomIO {{p}}) Random.Fin.randomRIO public

module Bool where

  open import Data.Bool.Base using (Bool; _≤_)
  open MkRandomIOInstances _≤_ Random.Bool.randomIO Random.Bool.randomRIO public

module List {a} {A : Set a} (rIO : IO A)  where

  open import Data.List.Base using (List)

  monadRandom : RawMonadRandom (List A) IO
  monadRandom = record { getRandom = Random.List.randomIO rIO }


open import Data.Nat.Base using (ℕ)

module Vec {a} {A : Set a} (rIO : IO A) (n : ℕ) where

  open import Data.Vec.Base using (Vec)

  monadRandom : RawMonadRandom (Vec A n) IO
  monadRandom = record { getRandom = Random.Vec.randomIO rIO n }

module Vec≤ {a} {A : Set a} (rIO : IO A) (n : ℕ) where

  open import Data.Vec.Bounded.Base using (Vec≤)

  monadRandom : RawMonadRandom (Vec≤ A n) IO
  monadRandom = record { getRandom = Random.Vec≤.randomIO rIO n }

module String where

  open import Data.String.Base using (String)

  monadRandom : RawMonadRandom String IO
  monadRandom = record { getRandom = Random.String.randomIO }

module String≤ (n : ℕ) where

  open import Data.String.Base using (String)

  monadRandom : RawMonadRandom String IO
  monadRandom = record { getRandom = Random.String≤.randomIO n }

open import Data.Char.Base using (Char; _≤_)

module RangedString≤ (a b : Char) .(a≤b : a ≤ b) (n : ℕ) where

  open import Data.String.Base using (String)

  monadRandom : RawMonadRandom String IO
  monadRandom = record { getRandom = Random.RangedString≤.randomIO a b a≤b n }

open import Effect.Monad.Reader.Transformer.Base

liftReaderT : RawMonadRandom A M → RawMonadRandom A (ReaderT B M)
liftReaderT rand = record
  { getRandom = mkReaderT (const Rand.getRandom)
  } where module Rand = RawMonadRandom rand

liftRReaderT : RawMonadRandomR A R M → RawMonadRandomR A R (ReaderT B M)
liftRReaderT randR = record
  { getRandom = mkReaderT (const RandR.getRandom)
  ; getRandomR = λ lo hi lo≤hi → mkReaderT (const (RandR.getRandomR lo hi lo≤hi))
  } where module RandR = RawMonadRandomR randR

open import Data.Product.Base using (_,_)
open import Effect.Monad.Writer.Transformer.Base

module _ {𝕎 : RawMonoid w g} where

  open RawMonoid 𝕎 renaming (Carrier to W)

  liftWriterT : RawFunctor M →
                RawMonadRandom A M →
                RawMonadRandom A (WriterT 𝕎 M)
  liftWriterT M rand = record
    { getRandom = mkWriterT (λ w → (w ,_) <$> Rand.getRandom)
    } where open RawFunctor M
            module Rand = RawMonadRandom rand

  liftRWriterT : RawFunctor M →
                 RawMonadRandomR A R M →
                 RawMonadRandomR A R (WriterT 𝕎 M)
  liftRWriterT M randR = record
    { getRandom = mkWriterT (λ w → (w ,_) <$> RandR.getRandom)
    ; getRandomR = λ lo hi lo≤hi → mkWriterT (λ w → (w ,_) <$> RandR.getRandomR lo hi lo≤hi)
    } where open RawFunctor M
            module RandR = RawMonadRandomR randR

open import Effect.Monad.State.Transformer.Base

liftStateT : RawFunctor M →
             RawMonadRandom A M →
             RawMonadRandom A (StateT S M)
liftStateT M rand = record
  { getRandom = mkStateT (λ w → (w ,_) <$> Rand.getRandom)
  } where open RawFunctor M
          module Rand = RawMonadRandom rand

liftRStateT : RawFunctor M →
              RawMonadRandomR A R M →
              RawMonadRandomR A R (StateT S M)
liftRStateT M randR = record
  { getRandom = mkStateT (λ s → (s ,_) <$> RandR.getRandom)
  ; getRandomR = λ lo hi lo≤hi → mkStateT (λ s → (s ,_) <$> RandR.getRandomR lo hi lo≤hi)
  } where open RawFunctor M
          module RandR = RawMonadRandomR randR


open import Data.Sum.Base using (inj₁; inj₂; [_,_]′)
open import Data.Sum.Effectful.Left.Transformer

liftSumₗT : RawFunctor M →
            RawMonadRandom A M →
            RawMonadRandom A (SumₗT E _ M)
liftSumₗT M rand = record
  { getRandom = mkSumₗT (inj₂ <$> Rand.getRandom)
  } where open RawFunctor M
          module Rand = RawMonadRandom rand

liftRSumₗT : RawFunctor M →
             RawMonadRandomR A R M →
             RawMonadRandomR A R (SumₗT E _ M)
liftRSumₗT M randR = record
  { getRandom = mkSumₗT (inj₂ <$> RandR.getRandom)
  ; getRandomR = λ lo hi lo≤hi → mkSumₗT (inj₂ <$> RandR.getRandomR lo hi lo≤hi)
  } where open RawFunctor M
          module RandR = RawMonadRandomR randR

open import Data.Sum.Effectful.Right.Transformer

liftSumᵣT : RawFunctor M →
            RawMonadRandom A M →
            RawMonadRandom A (SumᵣT _ E M)
liftSumᵣT M rand = record
  { getRandom = mkSumᵣT (inj₁ <$> Rand.getRandom)
  } where open RawFunctor M
          module Rand = RawMonadRandom rand

liftRSumᵣT : RawFunctor M →
             RawMonadRandomR A R M →
             RawMonadRandomR A R (SumᵣT _ E M)
liftRSumᵣT M randR = record
  { getRandom = mkSumᵣT (inj₁ <$> RandR.getRandom)
  ; getRandomR = λ lo hi lo≤hi → mkSumᵣT (inj₁ <$> RandR.getRandomR lo hi lo≤hi)
  } where open RawFunctor M
          module RandR = RawMonadRandomR randR
