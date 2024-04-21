------------------------------------------------------------------------
-- The Agda standard library
--
-- IO handles: simple bindings to Haskell types and functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module IO.Handle where

open import Level using (Level)
open import Data.Unit.Polymorphic.Base using (⊤)
open import IO.Base using (IO; lift; lift′)

private variable a : Level

------------------------------------------------------------------------
-- Re-exporting types and constructors

open import IO.Primitive.Handle as Prim public
  using ( BufferMode
        ; noBuffering
        ; lineBuffering
        ; blockBuffering
        ; Handle
        ; stdin
        ; stdout
        ; stderr
        )

------------------------------------------------------------------------
-- Wrapping functions

hSetBuffering : Handle → BufferMode → IO {a} ⊤
hSetBuffering hdl bm = lift′ (Prim.hSetBuffering hdl bm)

hGetBuffering : Handle → IO BufferMode
hGetBuffering hdl = lift (Prim.hGetBuffering hdl)

hFlush : Handle → IO {a} ⊤
hFlush hdl = lift′ (Prim.hFlush hdl)
