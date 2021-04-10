------------------------------------------------------------------------
-- The Agda standard library
--
-- IO
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module IO where

open import Codata.Musical.Notation
open import Codata.Musical.Costring
open import Data.Unit.Polymorphic.Base
open import Data.String.Base
import Data.Unit.Base as Unit0
open import Function.Base using (_∘_)
import IO.Primitive as Prim
open import Level

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Re-exporting the basic type and functions

open import IO.Base public

------------------------------------------------------------------------
-- Utilities

module Colist where

  open import Codata.Musical.Colist.Base

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

  mapM : (A → IO B) → Colist A → IO (Colist B)
  mapM f = sequence ∘ map f

  mapM′ : (A → IO B) → Colist A → IO ⊤
  mapM′ f = sequence′ ∘ map f

module List where

  open import Data.List.Base

  sequence : List (IO A) → IO (List A)
  sequence []       = ⦇ [] ⦈
  sequence (c ∷ cs) = ⦇ c ∷ sequence cs ⦈

  -- The reason for not defining sequence′ in terms of sequence is
  -- efficiency (the unused results could cause unnecessary memory use).

  sequence′ : List (IO A) → IO ⊤
  sequence′ []       = return _
  sequence′ (c ∷ cs) = c >> sequence′ cs

  mapM : (A → IO B) → List A → IO (List B)
  mapM f = sequence ∘ map f

  mapM′ : (A → IO B) → List A → IO ⊤
  mapM′ f = sequence′ ∘ map f

------------------------------------------------------------------------
-- Simple lazy IO

-- Note that the functions below produce commands which, when
-- executed, may raise exceptions.

-- Note also that the semantics of these functions depends on the
-- version of the Haskell base library. If the version is 4.2.0.0 (or
-- later?), then the functions use the character encoding specified by
-- the locale. For older versions of the library (going back to at
-- least version 3) the functions use ISO-8859-1.

open import IO.Finite public
  renaming (readFile to readFiniteFile)

open import IO.Infinite public
  renaming ( writeFile  to writeFile∞
           ; appendFile to appendFile∞
           ; putStr     to putStr∞
           ; putStrLn   to putStrLn∞
           )
