------------------------------------------------------------------------
-- The Agda standard library
--
-- Fancy display functions for Lists
-- This is a core module because we have (unenforced) invariants.
-- If you cannot guarantee that your data respects these invariants,
-- you should instead use Data.List.Show.
------------------------------------------------------------------------

module Data.List.Show.Core where

open import Data.Bool.Base using (if_then_else_)
open import Data.List.Base as List
  using (List; []; _∷_; _++_; _∷ʳ_; null; map; intersperse)
open import Data.Nat.Base
open import Data.String.Base as String
  using (String; unlines; replicate; length)
open import Function.Base
open import Agda.Builtin.Equality

-- /!\ Invariants:
-- * header as the same length as each one of the rows
-- * All of the Strings have the same length

table : List (List String) → String
table []              = ""
table (header ∷ rows) =
  unlines $ map String.concat
          $ th ++ (trs ∷ʳ bot) where

  bars : List String
  bars = map (λ cell → replicate (length cell) '─') header

  top sep bot : List String
  tr : List String → List String
  top =         ("┌" ∷ (intersperse "┬" bars ∷ʳ "┐"))
  tr  = λ tds → ("│" ∷ (intersperse "│" tds  ∷ʳ "│"))
  sep =         ("├" ∷ (intersperse "┼" bars ∷ʳ "┤"))
  bot =         ("└" ∷ (intersperse "┴" bars ∷ʳ "┘"))

  th  = top ∷ tr header ∷ []
  trs = if null rows then id else (sep ∷_)
      $ intersperse sep $ map tr rows

------------------------------------------------------------------------
-- examples

_ : table ( ("foo" ∷ "bar" ∷ [])
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

_ : table (("foo" ∷ "bar" ∷ []) ∷ [])
  ≡ "┌───┬───┐
\   \│foo│bar│
\   \└───┴───┘"
_ = refl

_ : table ( (" different " ∷ " sizes " ∷ [])
          ∷ ("   work    " ∷ "  too  " ∷ [])
          ∷ [])
  ≡ "┌───────────┬───────┐
\   \│ different │ sizes │
\   \├───────────┼───────┤
\   \│   work    │  too  │
\   \└───────────┴───────┘"
_ = refl
