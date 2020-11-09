------------------------------------------------------------------------
-- The Agda standard library
--
-- Printf-style versions of typeError and debugPrint
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.TypeChecking.Format where

open import Agda.Builtin.Reflection using (Name; Term; ErrorPart; termErr; nameErr; strErr;
                                           TC; typeError; debugPrint)
open import Level                   using (Level)
open import Function.Base           using (_∘_)
open import Data.List.Base          using (List; [_]; concat)
open import Data.Maybe.Base         using (Maybe; nothing; just)
open import Data.Nat.Base           using (ℕ)
open import Data.String.Base        using (String)
open import Data.Sum.Base           using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base          using (⊤)

import Text.Format as StdFormat using (formatSpec)
import Text.Printf as StdPrintf using (printfSpec)

open import Text.Format.Generic
open import Text.Printf.Generic

private
  variable
    ℓ : Level
    A : Set ℓ

------------------------------------------------------------------------
-- Format specification.
-- This extends the formats from Text.Printf with
--   %t  - Term
--   %q  - Name
--   %e  - List ErrorPart
-- Rendering goes to List ErrorPart.

module Specification where

  data ErrorChunk : Set where
    `Term `Name `Parts : ErrorChunk

  errorSpec : FormatSpec
  errorSpec .FormatSpec.ArgChunk = ErrorChunk
  errorSpec .FormatSpec.ArgType `Term  = Term
  errorSpec .FormatSpec.ArgType `Name  = Name
  errorSpec .FormatSpec.ArgType `Parts = List ErrorPart
  errorSpec .FormatSpec.lexArg 't'     = just `Term
  errorSpec .FormatSpec.lexArg 'q'     = just `Name
  errorSpec .FormatSpec.lexArg 'e'     = just `Parts
  errorSpec .FormatSpec.lexArg  _      = nothing

  formatSpec : FormatSpec
  formatSpec = unionSpec errorSpec StdFormat.formatSpec

  open PrintfSpec

  printfSpec : PrintfSpec formatSpec (List ErrorPart)
  printfSpec .renderArg (inj₁ `Term)  t  = [ termErr t ]
  printfSpec .renderArg (inj₁ `Name)  n  = [ nameErr n ]
  printfSpec .renderArg (inj₁ `Parts) es = es
  printfSpec .renderArg (inj₂ arg)    x  = [ strErr (StdPrintf.printfSpec .renderArg arg x) ]
  printfSpec .renderStr               s  = [ strErr s ]

open Specification

open Format formatSpec
open Type   formatSpec renaming (map to mapPrintf)
open Render printfSpec

------------------------------------------------------------------------
-- Printf versions of typeError and debugPrint

typeErrorFmt : (fmt : String) → Printf (lexer fmt) (TC A)
typeErrorFmt fmt = mapPrintf (lexer fmt) (typeError ∘ concat) (printf fmt)

debugPrintFmt : String → ℕ → (fmt : String) → Printf (lexer fmt) (TC ⊤)
debugPrintFmt tag lvl fmt = mapPrintf (lexer fmt) (debugPrint tag lvl ∘ concat) (printf fmt)

-- Combine with "%e" format for nested format calls.
errorPartFmt : (fmt : String) → Printf (lexer fmt) (List ErrorPart)
errorPartFmt fmt = mapPrintf (lexer fmt) concat (printf fmt)
