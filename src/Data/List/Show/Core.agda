------------------------------------------------------------------------
-- The Agda standard library
--
-- Fancy display functions for List
-- This is a core module because we have (unenforced) invariants.
-- If you cannot guarantee that your data respects these invariants,
-- you should instead use Data.List.Show.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Data.List.Show.Core where

open import Data.Bool.Base using (if_then_else_)
open import Data.Char.Base using (Char)
open import Data.List.Base as List
  using (List; []; _∷_; _?∷_; _++_; _∷ʳ?_; null; map; intersperse)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe)
open import Data.Nat.Base
open import Data.String.Base as String
  using (String; fromChar; unlines; replicate; length)
open import Function.Base
open import Agda.Builtin.Equality

record Line : Set where
  field left  : Maybe String
        cont  : Maybe Char
        sep   : String
        right : Maybe String
open Line

record Config : Set where
  field top : Maybe Line
        sep : Maybe Line
        row : Line
        bot : Maybe Line
open Config

unicode : Config
unicode .top = just λ where
  .left  → just "┌"
  .cont  → just '─'
  .sep   → "┬"
  .right → just "┐"
unicode .sep = just λ where
  .left  → just "├"
  .cont  → just '─'
  .sep   → "┼"
  .right → just "┤"
unicode .row = λ where
  .left  → just "│"
  .cont  → nothing
  .sep   → "│"
  .right → just "│"
unicode .bot = just λ where
  .left  → just "└"
  .cont  → just '─'
  .sep   → "┴"
  .right → just "┘"

ascii : Config
ascii .top = just λ where
  .left  → just "+"
  .cont  → just '-'
  .sep   → "-"
  .right → just "+"
ascii .sep = just λ where
  .left  → just "|"
  .cont  → just '-'
  .sep   → "+"
  .right → just "|"
ascii .row = λ where
  .left  → just "|"
  .cont  → nothing
  .sep   → "|"
  .right → just "|"
ascii .bot = just λ where
  .left  → just "+"
  .cont  → just '-'
  .sep   → "-"
  .right → just "+"

compact : Config → Config
compact c = record c { sep = nothing }

module _ where

  private
    dropBorder : Line → Line
    dropBorder l = record l { left = nothing; right = nothing }

  noborder : Config → Config
  noborder c .top = nothing
  noborder c .sep = Maybe.map dropBorder (c .sep)
  noborder c .row = dropBorder (c .row)
  noborder c .bot = nothing

module _ where

  private
    space : Line → Line
    space l = let pad = maybe fromChar " " (l .cont) in λ where
      .left  → Maybe.map (String._++ pad) (l .left)
      .cont  → l .cont
      .sep   → pad String.++ l .sep String.++ pad
      .right → Maybe.map (pad String.++_) (l .right)

  addSpace : Config → Config
  addSpace c .top = Maybe.map space (c .top)
  addSpace c .sep = Maybe.map space (c .sep)
  addSpace c .row = space (c .row)
  addSpace c .bot = Maybe.map space (c .bot)

whitespace : Config
whitespace .top = nothing
whitespace .sep = nothing
whitespace .row = λ where
  .left  → nothing
  .cont  → nothing
  .sep   → " "
  .right → nothing
whitespace .bot = nothing

-- /!\ Invariants:
-- * the table is presented as a list of rows
-- * header has the same length as each one of the rows
--   i.e. we have a rectangular table
-- * all of the strings in a given column have the same length

table : Config → List (List String) → String
table _ []              = ""
table c (header ∷ rows) =
  unlines $ map String.concat
          $ th ++ (trs ∷ʳ? lbot) where

  cellsOf : Maybe Char → List String → List String
  cellsOf nothing  = id
  cellsOf (just c) = map (λ cell → replicate (length cell) c)

  lineOf : Line → List String → List String
  lineOf l xs = l .left
            ?∷  intersperse (l .sep) (cellsOf (l .cont) xs)
            ∷ʳ? l .right

  mlineOf : Maybe Line → List String → Maybe (List String)
  mlineOf l xs = Maybe.map (λ l → lineOf l xs) l

  ltop : Maybe (List String)
  lsep : Maybe (List String)
  tr   : List String → List String
  lbot : Maybe (List String)

  ltop = mlineOf (c. top) header
  lsep = mlineOf (c. sep) header
  tr   = lineOf (c. row)
  lbot = mlineOf (c. bot) header

  th  = ltop ?∷ tr header ∷ []
  trs = if null rows then id else (maybe _∷_ id lsep)
      $ maybe intersperse id lsep
      $ map tr rows

------------------------------------------------------------------------
-- examples

_ : table unicode
          ( ("foo" ∷ "bar" ∷ [])
          ∷ ("  1" ∷ "  2" ∷ [])
          ∷ ("  4" ∷ "  3" ∷ [])
          ∷ [])
  ≡ "┌───┬───┐
\   \│foo│bar│
\   \├───┼───┤
\   \│  1│  2│
\   \├───┼───┤
\   \│  4│  3│
\   \└───┴───┘"
_ = refl

_ : table (noborder unicode)
          ( ("foo" ∷ "bar" ∷ [])
          ∷ ("  1" ∷ "  2" ∷ [])
          ∷ ("  4" ∷ "  3" ∷ [])
          ∷ [])
  ≡ "foo│bar
\   \───┼───
\   \  1│  2
\   \───┼───
\   \  4│  3"
_ = refl

_ : table (compact unicode)
          ( ("foo" ∷ "bar" ∷ [])
          ∷ ("  1" ∷ "  2" ∷ [])
          ∷ ("  4" ∷ "  3" ∷ [])
          ∷ [])
  ≡ "┌───┬───┐
\   \│foo│bar│
\   \│  1│  2│
\   \│  4│  3│
\   \└───┴───┘"
_ = refl

_ : table (noborder $ compact unicode)
          ( ("foo" ∷ "bar" ∷ [])
          ∷ ("  1" ∷ "  2" ∷ [])
          ∷ ("  4" ∷ "  3" ∷ [])
          ∷ [])
  ≡ "foo│bar
\   \  1│  2
\   \  4│  3"
_ = refl

_ : table (addSpace unicode)
          ( ("foo" ∷ "bar" ∷ [])
          ∷ ("  1" ∷ "  2" ∷ [])
          ∷ ("  4" ∷ "  3" ∷ [])
          ∷ [])
  ≡ "┌─────┬─────┐
\   \│ foo │ bar │
\   \├─────┼─────┤
\   \│   1 │   2 │
\   \├─────┼─────┤
\   \│   4 │   3 │
\   \└─────┴─────┘"
_ = refl

_ : table ascii
          ( ("foo" ∷ "bar" ∷ [])
          ∷ ("  1" ∷ "  2" ∷ [])
          ∷ ("  4" ∷ "  3" ∷ [])
          ∷ [])
  ≡ "+-------+
\   \|foo|bar|
\   \|---+---|
\   \|  1|  2|
\   \|---+---|
\   \|  4|  3|
\   \+-------+"
_ = refl

_ : table whitespace
          ( ("foo" ∷ "bar" ∷ [])
          ∷ ("  1" ∷ "  2" ∷ [])
          ∷ ("  4" ∷ "  3" ∷ [])
          ∷ [])
  ≡ "foo bar
\   \  1   2
\   \  4   3"
_ = refl

_ : table (compact ascii)
          ( ("foo" ∷ "bar" ∷ [])
          ∷ ("  1" ∷ "  2" ∷ [])
          ∷ ("  4" ∷ "  3" ∷ [])
          ∷ [])
  ≡ "+-------+
\   \|foo|bar|
\   \|  1|  2|
\   \|  4|  3|
\   \+-------+"
_ = refl

_ : table unicode (("foo" ∷ "bar" ∷ []) ∷ [])
  ≡ "┌───┬───┐
\   \│foo│bar│
\   \└───┴───┘"
_ = refl

_ : table unicode
          ( (" different " ∷ " sizes " ∷ [])
          ∷ ("   work    " ∷ "  too  " ∷ [])
          ∷ [])
  ≡ "┌───────────┬───────┐
\   \│ different │ sizes │
\   \├───────────┼───────┤
\   \│   work    │  too  │
\   \└───────────┴───────┘"
_ = refl
