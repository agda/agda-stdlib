------------------------------------------------------------------------
-- The Agda standard library
--
-- Fancy display functions for List-based tables
--
-- The functions in this module assume some (unenforced) invariants.
-- If you cannot guarantee that your data respects these invariants,
-- you should instead use Text.Tabular.List.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Text.Tabular.Base where

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

open String
  using ( Alignment
        ; Left
        ; Center
        ; Right
        ) public

record TabularLine : Set where
  field
    left  : Maybe String
    cont  : Maybe Char
    sep   : String
    right : Maybe String
open TabularLine

record TabularConfig : Set where
  field
    top : Maybe TabularLine
    sep : Maybe TabularLine
    row : TabularLine
    bot : Maybe TabularLine
open TabularConfig

unicode : TabularConfig
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

ascii : TabularConfig
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

compact : TabularConfig → TabularConfig
compact c = record c { sep = nothing }

private
  dropBorder : TabularLine → TabularLine
  dropBorder l = record l { left = nothing; right = nothing }

noBorder : TabularConfig → TabularConfig
noBorder c .top = nothing
noBorder c .sep = Maybe.map dropBorder (c .sep)
noBorder c .row = dropBorder (c .row)
noBorder c .bot = nothing


private
  space : TabularLine → TabularLine
  space l = let pad = maybe fromChar " " (l .cont) in λ where
    .left  → Maybe.map (String._++ pad) (l .left)
    .cont  → l .cont
    .sep   → pad String.++ l .sep String.++ pad
    .right → Maybe.map (pad String.++_) (l .right)

addSpace : TabularConfig → TabularConfig
addSpace c .top = Maybe.map space (c .top)
addSpace c .sep = Maybe.map space (c .sep)
addSpace c .row = space (c .row)
addSpace c .bot = Maybe.map space (c .bot)

whitespace : TabularConfig
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

unsafeDisplay : TabularConfig → List (List String) → List String
unsafeDisplay _ []              = []
unsafeDisplay c (header ∷ rows) =
  map String.concat $ th ++ (trs ∷ʳ? lbot) where

  cellsOf : Maybe Char → List String → List String
  cellsOf nothing  = id
  cellsOf (just c) = map (λ cell → replicate (length cell) c)

  lineOf : TabularLine → List String → List String
  lineOf l xs = l .left
            ?∷  intersperse (l .sep) (cellsOf (l .cont) xs)
            ∷ʳ? l .right

  mlineOf : Maybe TabularLine → List String → Maybe (List String)
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
