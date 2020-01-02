------------------------------------------------------------------------
-- The Agda standard library
--
-- Examples of printing list and vec-based tables
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module README.Text.Tabular where

open import Function.Base
open import Relation.Binary.PropositionalEquality

open import Data.List.Base
open import Data.String.Base
open import Data.Vec.Base

open import Text.Tabular.Base
import Text.Tabular.List as Tabularˡ
import Text.Tabular.Vec  as Tabularᵛ

------------------------------------------------------------------------
-- VEC
--
-- If you have a matrix of strings, you simply need to:
--   * pick a configuration (see below)
--   * pick an alignment for each column
--   * pass the matrix
--
-- The display function will then pad each string on the left, right,
-- or both to respect the alignment constraints.
-- It will return a list of strings corresponding to each line in the
-- table. You may then:
---  * use Data.String.Base's unlines to produce a String
--   * use Text.Pretty's text and vcat to produce a Doc (i.e. indentable!)
------------------------------------------------------------------------

_ : unlines (Tabularᵛ.display unicode
            (Right ∷ Left ∷ Center ∷ [])
          ( ("foo" ∷ "bar" ∷ "baz" ∷ [])
          ∷ ("1"   ∷ "2"   ∷ "3" ∷ [])
          ∷ ("6"   ∷ "5"   ∷ "4" ∷ [])
          ∷ []))
  ≡ "┌───┬───┬───┐
\   \│foo│bar│baz│
\   \├───┼───┼───┤
\   \│  1│2  │ 3 │
\   \├───┼───┼───┤
\   \│  6│5  │ 4 │
\   \└───┴───┴───┘"
_ = refl

------------------------------------------------------------------------
-- CONFIG
--
-- Configurations allow you to change the way the table is displayed.
------------------------------------------------------------------------

-- We will use the same example throughout

foobar : Vec (Vec String 2) 3
foobar = ("foo" ∷ "bar" ∷ [])
       ∷ ("1"   ∷ "2"   ∷ [])
       ∷ ("4"   ∷ "3"   ∷ [])
       ∷ []

------------------------------------------------------------------------
-- Basic configurations: unicode, ascii, whitespace

-- unicode

_ : unlines (Tabularᵛ.display unicode
            (Right ∷ Left ∷ [])
            foobar)
  ≡ "┌───┬───┐
\   \│foo│bar│
\   \├───┼───┤
\   \│  1│2  │
\   \├───┼───┤
\   \│  4│3  │
\   \└───┴───┘"
_ = refl

-- ascii

_ : unlines (Tabularᵛ.display ascii
            (Right ∷ Left ∷ [])
            foobar)
  ≡ "+-------+
\   \|foo|bar|
\   \|---+---|
\   \|  1|2  |
\   \|---+---|
\   \|  4|3  |
\   \+-------+"
_ = refl

-- whitespace

_ : unlines (Tabularᵛ.display whitespace
            (Right ∷ Left ∷ [])
            foobar)
  ≡ "foo bar
\   \  1 2  
\   \  4 3  "
_ = refl

------------------------------------------------------------------------
-- Modifiers: altering existing configurations

-- In these examples we will be using unicode as the base configuration.
-- However these modifiers apply to all configurations (and can even be
-- combined)

-- compact: drop the horizontal line between each row

_ : unlines (Tabularᵛ.display (compact unicode)
            (Right ∷ Left ∷ [])
            foobar)
  ≡ "┌───┬───┐
\   \│foo│bar│
\   \│  1│2  │
\   \│  4│3  │
\   \└───┴───┘"
_ = refl

-- noBorder: drop the outside borders

_ : unlines (Tabularᵛ.display (noBorder unicode)
            (Right ∷ Left ∷ [])
            foobar)
  ≡ "foo│bar
\   \───┼───
\   \  1│2  
\   \───┼───
\   \  4│3  "
_ = refl

-- addSpace : add whitespace space inside cells

_ : unlines (Tabularᵛ.display (addSpace unicode)
            (Right ∷ Left ∷ [])
            foobar)
  ≡ "┌─────┬─────┐
\   \│ foo │ bar │
\   \├─────┼─────┤
\   \│   1 │ 2   │
\   \├─────┼─────┤
\   \│   4 │ 3   │
\   \└─────┴─────┘"
_ = refl

-- compact together with addSpace

_ : unlines (Tabularᵛ.display (compact (addSpace unicode))
            (Right ∷ Left ∷ [])
            foobar)
  ≡ "┌─────┬─────┐
\   \│ foo │ bar │
\   \│   1 │ 2   │
\   \│   4 │ 3   │
\   \└─────┴─────┘"
_ = refl


------------------------------------------------------------------------
-- LIST
--
-- Same thing as for vectors except that if the list of lists is not
-- rectangular, it is padded with empty strings to make it so. If there
-- are not enough alignment directives, we arbitrarily pick Left.
------------------------------------------------------------------------

_ : unlines (Tabularˡ.display unicode
          (Center ∷ Right ∷ [])
          ( ("foo" ∷ "bar" ∷ [])
          ∷ ("partial" ∷ "rows" ∷ "are" ∷ "ok" ∷ [])
          ∷ ("3" ∷ "2" ∷ "1" ∷ "..." ∷ "surprise!" ∷ [])
          ∷ []))
  ≡ "┌───────┬────┬───┬───┬─────────┐
\   \│  foo  │ bar│   │   │         │
\   \├───────┼────┼───┼───┼─────────┤
\   \│partial│rows│are│ok │         │
\   \├───────┼────┼───┼───┼─────────┤
\   \│   3   │   2│1  │...│surprise!│
\   \└───────┴────┴───┴───┴─────────┘"
_ = refl

------------------------------------------------------------------------
-- LIST (UNSAFE)
--
-- If you know *for sure* that your data is already perfectly rectangular
-- i.e. all the rows of the list of lists have the same length
--      in each column, all the strings have the same width
-- then you can use the unsafeDisplay function defined Text.Tabular.Base.
--
-- This is what gets used internally by `Text.Tabular.Vec` and
-- `Text.Tabular.List` once the potentially unsafe data has been
-- processed.
------------------------------------------------------------------------

_ : unlines (unsafeDisplay (compact unicode)
          ( ("foo" ∷ "bar" ∷ [])
          ∷ ("  1" ∷ "  2" ∷ [])
          ∷ ("  4" ∷ "  3" ∷ [])
          ∷ []))
  ≡ "┌───┬───┐
\   \│foo│bar│
\   \│  1│  2│
\   \│  4│  3│
\   \└───┴───┘"
_ = refl
