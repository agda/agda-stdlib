------------------------------------------------------------------------
-- The Agda standard library
--
-- IO: basic types and functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module IO.Base where

open import Codata.Musical.Notation
open import Data.Unit.Polymorphic.Base
import IO.Primitive as Prim
open import Level

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- The IO monad

-- One cannot write "infinitely large" computations with the
-- postulated IO monad in IO.Primitive without turning off the
-- termination checker (or going via the FFI, or perhaps abusing
-- something else). The following coinductive deep embedding is
-- introduced to avoid this problem. Possible non-termination is
-- isolated to the run function below.

data IO (A : Set a) : Set (suc a) where
  lift   : (m : Prim.IO A) → IO A
  return : (x : A) → IO A
  bind   : {B : Set a} (m : ∞ (IO B)) (f : (x : B) → ∞ (IO A)) → IO A
  seq    : {B : Set a} (m₁ : ∞ (IO B)) (m₂ : ∞ (IO A)) → IO A

pure : A → IO A
pure = return

module _ {A B : Set a} where

  infixl 1 _<$>_ _<*>_ _>>=_ _>>_

  _<*>_ : IO (A → B) → IO A → IO B
  mf <*> mx = bind (♯ mf) λ f → ♯ (bind (♯ mx) λ x → ♯ pure (f x))

  _<$>_ : (A → B) → IO A → IO B
  f <$> m = pure f <*> m

  _>>=_ : IO A → (A → IO B) → IO B
  m >>= f = bind (♯ m) λ x → ♯ f x

  _>>_ : IO A → IO B → IO B
  m₁ >> m₂ = seq (♯ m₁) (♯ m₂)

------------------------------------------------------------------------
-- Running programs

-- A value of type `IO A` is a description of a computation that may
-- eventually produce an `A`. The `run` function converts this description
-- of a computation into calls to primitive functions that will actually
-- perform it.

{-# NON_TERMINATING #-}
run : IO A → Prim.IO A
run (lift m)    = m
run (return x)  = Prim.return x
run (bind m f)  = run (♭ m ) Prim.>>= λ x → run (♭ (f x))
run (seq m₁ m₂) = run (♭ m₁) Prim.>>= λ _ → run (♭ m₂)

-- The entrypoint of an Agda program will be assigned type `Main` and
-- implemented using `run` on some `IO ⊤` program.

Main : Set
Main = Prim.IO {0ℓ} ⊤

------------------------------------------------------------------------
-- Utilities

ignore : IO A → IO ⊤
ignore io = io >> return _
