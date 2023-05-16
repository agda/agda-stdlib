------------------------------------------------------------------------
-- The Agda standard library
--
-- IO: basic types and functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module IO.Base where

open import Level
open import Codata.Musical.Notation
open import Data.Bool.Base using (Bool; true; false; not)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Agda.Builtin.Unit as Unit0
open import Data.Unit.Polymorphic.Base
open import Function.Base using (_∘′_; const; flip)
import IO.Primitive as Prim

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
  lift : (m : Prim.IO A) → IO A
  pure : (x : A) → IO A
  bind : {B : Set a} (m : ∞ (IO B)) (f : (x : B) → ∞ (IO A)) → IO A
  seq  : {B : Set a} (m₁ : ∞ (IO B)) (m₂ : ∞ (IO A)) → IO A

lift! : IO A → IO (Lift b A)
lift!         (lift io)   = lift (io Prim.>>= λ a → Prim.pure (Level.lift a))
lift!         (pure a)    = pure (Level.lift a)
lift! {b = b} (bind m f)  = bind (♯ lift! {b = b} (♭ m))
                                 (λ x → ♯ lift! (♭ (f (lower x))))
lift! {b = b} (seq m₁ m₂) = seq (♯ lift! {b = b} (♭ m₁))
                                (♯ lift! (♭ m₂))

module _ {A B : Set a} where

  infixl 1 _<$>_ _<*>_ _>>=_ _>>_
  infixr 1 _=<<_

  _<*>_ : IO (A → B) → IO A → IO B
  mf <*> mx = bind (♯ mf) λ f → ♯ (bind (♯ mx) λ x → ♯ pure (f x))

  _<$>_ : (A → B) → IO A → IO B
  f <$> m = pure f <*> m

  _<$_ : B → IO A → IO B
  b <$ m = (const b) <$> m

  _>>=_ : IO A → (A → IO B) → IO B
  m >>= f = bind (♯ m) λ x → ♯ f x

  _=<<_ : (A → IO B) → IO A → IO B
  _=<<_ = flip _>>=_

  _>>_ : IO A → IO B → IO B
  m₁ >> m₂ = seq (♯ m₁) (♯ m₂)

  _<<_ : IO B → IO A → IO B
  _<<_ = flip _>>_

------------------------------------------------------------------------
-- Running programs

-- A value of type `IO A` is a description of a computation that may
-- eventually produce an `A`. The `run` function converts this description
-- of a computation into calls to primitive functions that will actually
-- perform it.

{-# NON_TERMINATING #-}
run : IO A → Prim.IO A
run (lift m)    = m
run (pure x)    = Prim.pure x
run (bind m f)  = run (♭ m ) Prim.>>= λ x → run (♭ (f x))
run (seq m₁ m₂) = run (♭ m₁) Prim.>>= λ _ → run (♭ m₂)

-- The entrypoint of an Agda program will be assigned type `Main` and
-- implemented using `run` on some `IO ⊤` program.

Main : Set
Main = Prim.IO {0ℓ} ⊤

------------------------------------------------------------------------
-- Utilities

-- Make a unit-returning primitive level polymorphic
lift′ : Prim.IO Unit0.⊤ → IO {a} ⊤
lift′ io = lift (io Prim.>>= λ _ → Prim.pure _)

-- Throw away the result
ignore : IO A → IO ⊤
ignore io = io >> pure _

-- Conditional executions
when : Bool → IO {a} ⊤ → IO ⊤
when true m = m
when false _ = pure _

unless : Bool → IO {a} ⊤ → IO ⊤
unless = when ∘′ not

whenJust : Maybe A → (A → IO {a} ⊤) → IO ⊤
whenJust (just a) k = k a
whenJust nothing  _ = pure _

-- Keep running an IO action until we get a value. Convenient when user
-- input is involved and it may be malformed.
untilJust : IO (Maybe A) → IO A
-- Note that here we are forced to use `bind` & the musical notation
-- explicitly to guarantee that the corecursive call is guarded
untilJust m = bind (♯ m) λ where
  nothing  → ♯ untilJust m
  (just a) → ♯ pure a

untilRight : {A B : Set a} → (A → IO (A ⊎ B)) → A → IO B
untilRight f x = bind (♯ f x) λ where
  (inj₁ x′) → ♯ untilRight f x′
  (inj₂ y) → ♯ pure y
