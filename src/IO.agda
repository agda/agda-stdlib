------------------------------------------------------------------------
-- The Agda standard library
--
-- IO
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module IO where

open import Codata.Musical.Notation
open import Codata.Musical.Costring
open import Data.Unit.Polymorphic
open import Data.String
import Data.Unit as Unit0
open import Function
import IO.Primitive as Prim
open import Level

private
  variable
    a b : Level

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

pure : {A : Set a} → A → IO A
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
-- of a computation into calls to primitve functions that will actually
-- perform it.

{-# NON_TERMINATING #-}
run : {A : Set a} → IO A → Prim.IO A
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

module Colist where

  open import Codata.Musical.Colist

  module _  {A : Set a} where

    sequence : Colist (IO A) → IO (Colist A)
    sequence []       = return []
    sequence (c ∷ cs) = bind (♯ c)               λ x  → ♯
                        bind (♯ sequence (♭ cs)) λ xs → ♯
                        return (x ∷ ♯ xs)

    -- The reason for not defining sequence′ in terms of sequence is
    -- efficiency (the unused results could cause unnecessary memory use).

    sequence′ : Colist (IO A) → IO ⊤
    sequence′ []       = return _
    sequence′ (c ∷ cs) = seq (♯ c) (♯ sequence′ (♭ cs))

  module _ {A : Set a} {B : Set b} where

    mapM : (A → IO B) → Colist A → IO (Colist B)
    mapM f = sequence ∘ map f

    mapM′ : (A → IO B) → Colist A → IO ⊤
    mapM′ f = sequence′ ∘ map f

module List where

  open import Data.List.Base

  module _  {A : Set a} where

    sequence : List (IO A) → IO (List A)
    sequence []       = ⦇ [] ⦈
    sequence (c ∷ cs) = ⦇ c ∷ sequence cs ⦈

    -- The reason for not defining sequence′ in terms of sequence is
    -- efficiency (the unused results could cause unnecessary memory use).

    sequence′ : List (IO A) → IO ⊤
    sequence′ []       = return _
    sequence′ (c ∷ cs) = c >> sequence′ cs

  module _ {A : Set a} {B : Set b} where

    mapM : (A → IO B) → List A → IO (List B)
    mapM f = sequence ∘ map f

    mapM′ : (A → IO B) → List A → IO ⊤
    mapM′ f = sequence′ ∘ map f

ignore : ∀ {a} {A : Set a} → IO A → IO ⊤
ignore io = io >> return _

------------------------------------------------------------------------
-- Simple lazy IO

-- Note that the functions below produce commands which, when
-- executed, may raise exceptions.

-- Note also that the semantics of these functions depends on the
-- version of the Haskell base library. If the version is 4.2.0.0 (or
-- later?), then the functions use the character encoding specified by
-- the locale. For older versions of the library (going back to at
-- least version 3) the functions use ISO-8859-1.

getLine : IO String
getLine = lift Prim.getLine

getContents : IO Costring
getContents = lift Prim.getContents

readFile : String → IO Costring
readFile f = lift (Prim.readFile f)

-- Reads a finite file. Raises an exception if the file path refers to
-- a non-physical file (like "/dev/zero").

readFiniteFile : String → IO String
readFiniteFile f = lift (Prim.readFiniteFile f)

private
  lift′ : Prim.IO Unit0.⊤ → IO {a} ⊤
  lift′ io = lift (io Prim.>>= λ _ → Prim.return _)

writeFile∞ : String → Costring → IO {a} ⊤
writeFile∞ f s = lift′ (Prim.writeFile f s)

writeFile : String → String → IO {a} ⊤
writeFile f s = writeFile∞ f (toCostring s)

appendFile∞ : String → Costring → IO {a} ⊤
appendFile∞ f s = lift′ (Prim.appendFile f s)

appendFile : String → String → IO {a} ⊤
appendFile f s = appendFile∞ f (toCostring s)

putStr∞ : Costring → IO {a} ⊤
putStr∞ s = lift′ (Prim.putStr s)

putStr : String → IO {a} ⊤
putStr s = putStr∞ (toCostring s)

putStrLn∞ : Costring → IO {a} ⊤
putStrLn∞ s = lift′ (Prim.putStrLn s)

putStrLn : String → IO {a} ⊤
putStrLn s = putStrLn∞ (toCostring s)

-- Note that the commands writeFile, appendFile, putStr and putStrLn
-- perform two conversions (string → costring → Haskell list). It may
-- be preferable to only perform one conversion.
