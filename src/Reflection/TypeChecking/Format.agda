------------------------------------------------------------------------
-- The Agda standard library
--
-- Printf-style formatting functions for type errors and debug printing.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.TypeChecking.Format where

open import Agda.Builtin.Reflection using (Name; Term; ErrorPart; termErr; nameErr; strErr;
                                           TC; typeError; debugPrint)
open import Function                using (_∘_)
open import Data.Char               using (Char)
open import Data.List               using (List; _∷_; []; [_]; _++_; map)
open import Data.Nat                using (ℕ)
open import Data.Nat.Show           using (show)
open import Data.String             using (String; toList; fromList)
open import Data.Unit               using (⊤)
open import Level                   using (Level)

private

  variable
    ℓ   : Level
    A B : Set ℓ

  data Format (Str : Set) : Set where
    litStr  : (s : Str) → Format Str
    termArg : Format Str
    nameArg : Format Str
    natArg  : Format Str
    strArg  : Format Str
    errArg  : Format Str

  mapFormat : (A → B) → Format A → Format B
  mapFormat f (litStr s) = litStr (f s)
  mapFormat f termArg    = termArg
  mapFormat f nameArg    = nameArg
  mapFormat f natArg     = natArg
  mapFormat f strArg     = strArg
  mapFormat f errArg     = errArg

  consChar : A → List (Format (List A)) → List (Format (List A))
  consChar c (litStr s ∷ fmt) = litStr (c ∷ s) ∷ fmt
  consChar c fmt              = litStr [ c ] ∷ fmt

  parseFormat′ : List Char → List (Format (List Char))
  parseFormat′ [] = []
  parseFormat′ ('%' ∷ 't' ∷ cs) = termArg ∷ parseFormat′ cs
  parseFormat′ ('%' ∷ 'n' ∷ cs) = nameArg ∷ parseFormat′ cs
  parseFormat′ ('%' ∷ 'd' ∷ cs) = natArg  ∷ parseFormat′ cs
  parseFormat′ ('%' ∷ 's' ∷ cs) = strArg  ∷ parseFormat′ cs
  parseFormat′ ('%' ∷ 'e' ∷ cs) = errArg  ∷ parseFormat′ cs
  parseFormat′ ('%' ∷ '%' ∷ cs) = consChar '%' (parseFormat′ cs)
  parseFormat′ (c ∷ cs)         = consChar c (parseFormat′ cs)

  parseFormat : String → List (Format String)
  parseFormat = map (mapFormat fromList) ∘ parseFormat′ ∘ toList

  FormatType′ : List (Format A) → Set ℓ → Set ℓ
  FormatType′ [] B = B
  FormatType′ (litStr s ∷ fmt) B =                  FormatType′ fmt B
  FormatType′ (termArg  ∷ fmt) B = Term           → FormatType′ fmt B
  FormatType′ (nameArg  ∷ fmt) B = Name           → FormatType′ fmt B
  FormatType′ (natArg   ∷ fmt) B = ℕ              → FormatType′ fmt B
  FormatType′ (strArg   ∷ fmt) B = String         → FormatType′ fmt B
  FormatType′ (errArg   ∷ fmt) B = List ErrorPart → FormatType′ fmt B

  FormatType : String → Set → Set
  FormatType fmt = FormatType′ (parseFormat fmt)

  formatError′ : (List ErrorPart → A) → (fmt : List (Format String)) → FormatType′ fmt A
  formatError′ fun []                 = fun []
  formatError′ fun (litStr s ∷ fmt)   = formatError′ (fun ∘ (strErr s        ∷_)) fmt
  formatError′ fun (termArg  ∷ fmt) t = formatError′ (fun ∘ (termErr t       ∷_)) fmt
  formatError′ fun (nameArg  ∷ fmt) x = formatError′ (fun ∘ (nameErr x       ∷_)) fmt
  formatError′ fun (natArg   ∷ fmt) n = formatError′ (fun ∘ (strErr (show n) ∷_)) fmt
  formatError′ fun (strArg   ∷ fmt) s = formatError′ (fun ∘ (strErr s        ∷_)) fmt
  formatError′ fun (errArg   ∷ fmt) e = formatError′ (fun ∘ (e              ++_)) fmt

-- Public API --

-- Supported formats:
--   %t  - Term
--   %n  - Name
--   %d  - ℕ
--   %s  - String
--   %e  - List ErrorPart
--   %%  - Single %

formatError : (List ErrorPart → A) → (fmt : String) → FormatType fmt A
formatError fun fmt = formatError′ fun (parseFormat fmt)

typeErrorFmt : (fmt : String) → FormatType fmt (TC A)
typeErrorFmt = formatError typeError

debugPrintFmt : String → ℕ → (fmt : String) → FormatType fmt (TC ⊤)
debugPrintFmt tag lvl = formatError (debugPrint tag lvl)
