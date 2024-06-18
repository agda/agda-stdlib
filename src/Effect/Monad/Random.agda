------------------------------------------------------------------------
-- The Agda standard library
--
-- The Random monad class
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module Effect.Monad.Random where

open import Effect.Functor using (RawFunctor)
open import Function.Base using (id)
open import IO.Base using (IO)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel)

open import System.Random as Random using (RandomRIO; InBounds)

private
  variable
    f g : Level
    A : Set f
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
    getRandomR : (lo hi : A) → .(lo ≤ hi) → M (InBounds _≤_ lo hi)

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

  open import Data.Word.Base using (Word64; _≤_)
  open MkRandomIOInstances _≤_ Random.Word64.randomIO Random.Word64.randomRIO public

module Fin where

  open import Data.Nat.Base using (ℕ; NonZero)
  open import Data.Fin.Base using (Fin; _≤_)

  module _ (n : ℕ) .{{p : NonZero n}} where
    open MkRandomIOInstances _≤_ (Random.Fin.randomIO {{p}}) Random.Fin.randomRIO public


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

module RangedString≤ (a b : Char)  .(a≤b : a ≤ b) (n : ℕ) where

  open import Data.String.Base using (String)

  monadRandom : RawMonadRandom String IO
  monadRandom = record { getRandom = Random.RangedString≤.randomIO a b a≤b n }
