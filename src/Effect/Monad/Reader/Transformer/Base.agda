------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic type and definition of the reader monad transformer
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Monad.Reader.Transformer.Base {r} (R : Set r) where

open import Level using (Level; suc; _⊔_)
open import Function.Base using (id)

private
  variable
    g : Level
    A : Set r

------------------------------------------------------------------------
-- Reader monad operations

record RawMonadReader
       (M : Set r → Set g)
       : Set (suc r ⊔ g) where
  field
    reader : (R → A) → M A
    local  : (R → R) → M A → M A

  ask : M R
  ask = reader id

------------------------------------------------------------------------
-- Reader monad transformer

record ReaderT
       (M : Set r → Set g)
       (A : Set r)
       : Set (r ⊔ g) where
  constructor mkReaderT
  field runReaderT : R → M A
open ReaderT public
