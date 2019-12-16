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
-- If you hae a matrix of strings, you simply need to:
--   * pick a configuration (see below)
--   * pick an alignment for each column
--   * pass the matrix
--
-- The display function will then pad each string on the left, right,
-- or both to respect the alignment constraints.
------------------------------------------------------------------------

_ : Tabularᵛ.display unicode
            (Right ∷ Left ∷ Center ∷ [])
          ( ("foo" ∷ "bar" ∷ "baz" ∷ [])
          ∷ ("1"   ∷ "2"   ∷ "3" ∷ [])
          ∷ ("6"   ∷ "5"   ∷ "4" ∷ [])
          ∷ [])
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

_ : Tabularᵛ.display unicode
            (Right ∷ Left ∷ [])
            foobar
  ≡ "┌───┬───┐
\   \│foo│bar│
\   \├───┼───┤
\   \│  1│2  │
\   \├───┼───┤
\   \│  4│3  │
\   \└───┴───┘"
_ = refl

-- ascii

_ : Tabularᵛ.display ascii
            (Right ∷ Left ∷ [])
            foobar
  ≡ "+-------+
\   \|foo|bar|
\   \|---+---|
\   \|  1|2  |
\   \|---+---|
\   \|  4|3  |
\   \+-------+"
_ = refl

-- whitespace

_ : Tabularᵛ.display whitespace
            (Right ∷ Left ∷ [])
            foobar
  ≡ "foo bar
\   \  1 2  
\   \  4 3  "
_ = refl

------------------------------------------------------------------------
-- Modifiers: altering existing configurations

-- In these examples we will be using unicode as the base configuration.
-- However these modifiers apply to all configuration (and can even be
-- combined)

-- compact: drop the horizontal line between each row

_ : Tabularᵛ.display (compact unicode)
            (Right ∷ Left ∷ [])
            foobar
  ≡ "┌───┬───┐
\   \│foo│bar│
\   \│  1│2  │
\   \│  4│3  │
\   \└───┴───┘"
_ = refl

-- noborder: drop the outside borders

_ : Tabularᵛ.display (noborder unicode)
            (Right ∷ Left ∷ [])
            foobar
  ≡ "foo│bar
\   \───┼───
\   \  1│2  
\   \───┼───
\   \  4│3  "
_ = refl

-- addspace : add whitespace space inside cells

_ : Tabularᵛ.display (addspace unicode)
            (Right ∷ Left ∷ [])
            foobar
  ≡ "┌─────┬─────┐
\   \│ foo │ bar │
\   \├─────┼─────┤
\   \│   1 │ 2   │
\   \├─────┼─────┤
\   \│   4 │ 3   │
\   \└─────┴─────┘"
_ = refl

-- compact together with addspace

_ : Tabularᵛ.display (compact (addspace unicode))
            (Right ∷ Left ∷ [])
            foobar
  ≡ "┌─────┬─────┐
\   \│ foo │ bar │
\   \│   1 │ 2   │
\   \│   4 │ 3   │
\   \└─────┴─────┘"
_ = refl


------------------------------------------------------------------------
-- LIST
--
-- Same thing as for vectors except that if the list of list is not
-- rectangular, it is padded with empty strings to make it so. If there
-- not enough alignment directives, we arbitrarily pick Left.
------------------------------------------------------------------------

_ : Tabularˡ.display unicode
          (Center ∷ Right ∷ [])
          ( ("foo" ∷ "bar" ∷ [])
          ∷ ("partial" ∷ "rows" ∷ "are" ∷ "ok" ∷ [])
          ∷ ("3" ∷ "2" ∷ "1" ∷ "..." ∷ "surprise!" ∷ [])
          ∷ [])
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

_ : unsafeDisplay (compact unicode)
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
