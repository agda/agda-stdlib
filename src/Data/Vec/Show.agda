------------------------------------------------------------------------
-- The Agda standard library
--
-- Fancy display functions for Vec
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Data.Vec.Show where

import Data.List.Show.Core as Show
open import Data.Vec.Base
open import Data.String.Base as String using (String)
open import Function.Base
open import Agda.Builtin.Equality

table : ∀ {m n} → Show.Config → Vec (Vec String n) m → String
table c = Show.table c
        ∘ toList
        ∘ map toList
        ∘ transpose
        ∘ map (String.rectangleˡ ' ')
        ∘ transpose

_ : table Show.unicode
          ( ("foo" ∷ "bar" ∷ [])
          ∷ ("1"   ∷ "2"   ∷ [])
          ∷ ("4"   ∷ "3"   ∷ [])
          ∷ [])
  ≡ "┌───┬───┐
\   \│foo│bar│
\   \├───┼───┤
\   \│  1│  2│
\   \├───┼───┤
\   \│  4│  3│
\   \└───┴───┘"
_ = refl
