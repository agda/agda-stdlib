------------------------------------------------------------------------
-- The Agda standard library
--
-- Examples of format strings and printf
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module README.Text where

open import Data.Nat.Base
open import Data.Char.Base
open import Data.List.Base
open import Data.String.Base
open import Data.Sum.Base

open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Format strings

open import Text.Format

-- We can specify a format by writing a string which will get interpreted
-- by a lexer into a list of formatting directives.

-- The specification types are always started with a '%' character:

-- Integers (%d or %i)
-- Naturals (%u)
-- Floats   (%f)
-- Chars    (%c)
-- Strings  (%s)

-- Anything which is not a type specification is a raw string to be spliced
-- in the output of printf.

-- For instance the following format alternates types and raw strings

_ : lexer "%s: %u + %u ≡ %u"
  ≡ inj₂ (`String ∷ Raw ": " ∷ `ℕ ∷ Raw " + " ∷ `ℕ ∷ Raw " ≡ " ∷ `ℕ ∷ [])
_ = refl

-- Lexing can fail. There are two possible errors:

-- If we start a specification type with a '%' but the string ends then
-- we get an UnexpectedEndOfString error

_ : lexer "%s: %u + %u ≡ %"
  ≡ inj₁ (UnexpectedEndOfString "%s: %u + %u ≡ %")
_ = refl

-- If we start a specification type with a '%' and the following character
-- does not correspond to an existing type, we get an InvalidType error
-- together with a focus highlighting the position of the problematic type.

_ : lexer "%s: %u + %a ≡ %u"
  ≡ inj₁ (InvalidType "%s: %u + %" 'a' " ≡ %u")
_ = refl

------------------------------------------------------------------------
-- Printf

open import Text.Printf

-- printf is a function which takes a format string as an argument and
-- returns a function expecting a value for each type specification present
-- in the format and returns a string splicing in these values into the
-- format string.

-- For instance `printf "%s: %u + %u ≡ %u"` is a
-- `String → ℕ → ℕ → ℕ → String` function.

_ : String → ℕ → ℕ → ℕ → String
_ = printf "%s: %u + %u ≡ %u"

_ : printf "%s: %u + %u ≡ %u" "example" 3 2 5
  ≡ "example: 3 + 2 ≡ 5"
_ = refl

-- If the format string str is invalid then `printf str` will have type
-- `Error e` where `e` is the lexing error.

_ : Text.Printf.Error (UnexpectedEndOfString "%s: %u + %u ≡ %")
_ = printf "%s: %u + %u ≡ %"

_ : Text.Printf.Error (InvalidType "%s: %u + %" 'a' " ≡ %u")
_ = printf "%s: %u + %a ≡ %u"

-- Trying to pass arguments to such an ̀Error` type will lead to a
-- unification error which hopefully makes the problem clear e.g.
-- `printf "%s: %u + %a ≡ %u" "example" 3 2 5` fails with the error:

-- Text.Printf.Error
-- (InvalidType
-- (fromList
--  (reverse
--   ('%' ∷ ' ' ∷ '+' ∷ ' ' ∷ 'u' ∷ '%' ∷ ' ' ∷ ':' ∷ 's' ∷ '%' ∷ [])))
-- 'a' (fromList (' ' ∷ '≡' ∷ ' ' ∷ '%' ∷ 'u' ∷ [])))
-- should be a function type, but it isn't
-- when checking that "example" 3 2 5 are valid arguments to a
-- function of type Text.Printf.Printf (lexer "%s: %u + %a ≡ %u")
