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

infixl 1 _‵bind‵_ _‵seq‵_

data IO (A : Set a) : Set (suc a) where
  lift     : (m : Prim.IO A) → IO A
  return   : (x : A) → IO A
  _‵bind‵_ : {B : Set a} (m : ∞ (IO B)) (f : (x : B) → ∞ (IO A)) → IO A
  _‵seq‵_  : {B : Set a} (m₁ : ∞ (IO B)) (m₂ : ∞ (IO A)) → IO A

pure : {A : Set a} → A → IO A
pure = return

module _ {A B : Set a} where

  infixl 1 _<*>_ _>>=_ _>>_

  _<*>_ : IO (A → B) → IO A → IO B
  mf <*> mx = ♯ mf ‵bind‵ λ f → ♯ (♯ mx ‵bind‵ λ x → ♯ pure (f x))

  _>>=_ : IO A → (A → IO B) → IO B
  m >>= f = ♯ m ‵bind‵ λ x → ♯ f x

  _>>_ : IO A → IO B → IO B
  m₁ >> m₂ = ♯ m₁ ‵seq‵ ♯ m₂

{-# NON_TERMINATING #-}

run : {A : Set a} → IO A → Prim.IO A
run (lift m)   = m
run (return x) = Prim.return x
run (m  ‵bind‵ f) = Prim._>>=_ (run (♭ m )) λ x → run (♭ (f x))
run (m₁ ‵seq‵ m₂) = Prim._>>=_ (run (♭ m₁)) λ _ → run (♭ m₂)

------------------------------------------------------------------------
-- Utilities

module Colist where

  open import Codata.Musical.Colist

  module _  {A : Set a} where

    sequence : Colist (IO A) → IO (Colist A)
    sequence []       = return []
    sequence (c ∷ cs) = ♯ c                  ‵bind‵ λ x  →
                        ♯ (♯ sequence (♭ cs) ‵bind‵ λ xs →
                        ♯ return (x ∷ ♯ xs))

    -- The reason for not defining sequence′ in terms of sequence is
    -- efficiency (the unused results could cause unnecessary memory use).

    sequence′ : Colist (IO A) → IO ⊤
    sequence′ []       = return _
    sequence′ (c ∷ cs) = ♯ c ‵seq‵ ♯ sequence′ (♭ cs)

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

getContents : IO Costring
getContents = lift Prim.getContents

readFile : String → IO Costring
readFile f = lift (Prim.readFile f)

-- Reads a finite file. Raises an exception if the file path refers to
-- a non-physical file (like "/dev/zero").

readFiniteFile : String → IO String
readFiniteFile f = lift (Prim.readFiniteFile f)

writeFile∞ : String → Costring → IO ⊤
writeFile∞ f s = ignore (lift (Prim.writeFile f s))

writeFile : String → String → IO ⊤
writeFile f s = writeFile∞ f (toCostring s)

appendFile∞ : String → Costring → IO ⊤
appendFile∞ f s = ignore (lift (Prim.appendFile f s))

appendFile : String → String → IO ⊤
appendFile f s = appendFile∞ f (toCostring s)

putStr∞ : Costring → IO ⊤
putStr∞ s = ignore (lift (Prim.putStr s))

putStr : String → IO ⊤
putStr s = putStr∞ (toCostring s)

putStrLn∞ : Costring → IO ⊤
putStrLn∞ s = ignore (lift (Prim.putStrLn s))

putStrLn : String → IO ⊤
putStrLn s = putStrLn∞ (toCostring s)

-- Note that the commands writeFile, appendFile, putStr and putStrLn
-- perform two conversions (string → costring → Haskell list). It may
-- be preferable to only perform one conversion.
