------------------------------------------------------------------------
-- The Agda standard library
--
-- Fancy display functions for Vec
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Data.Vec.Show where

import Data.List.Show.Core as Show
open import Data.Product as Prod using (uncurry)
open import Data.Vec.Base
open import Data.String.Base as String
  using (String; Align; fromAlign); open Align
open import Function.Base
open import Agda.Builtin.Equality

table : ∀ {m n} → Show.Config → Vec Align n → Vec (Vec String n) m → String
table c a = Show.table c
          ∘ toList
          ∘ map toList
          ∘ transpose
          ∘ map (uncurry String.rectangle ∘ unzip)
          ∘ transpose
          ∘ map (zip (map fromAlign a))

_ : table Show.unicode
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
