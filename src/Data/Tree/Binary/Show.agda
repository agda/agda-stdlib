------------------------------------------------------------------------
-- The Agda standard library
--
-- 1 dimensional pretty printing of binary trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Level using (Level)
open import Data.List.Base as List using (List; []; [_]; _∷_; _∷ʳ_)
open import Data.String.Base using (String)
import Data.Tree.Rose as Rose
import Data.Tree.Rose.Show as Rose
open import Data.Tree.Binary using (Tree; map)
open import Function.Base using (_∘′_; id)

module Data.Tree.Binary.Show where

private
  variable
    a : Level
    N L : Set a

display : Tree (List String) (List String) → List String
display = Rose.display ∘′ Rose.fromBinary id id

show : (N → List String) → (L → List String) → Tree N L → List String
show nodeStr leafStr = display ∘′ map nodeStr leafStr

showSimple : (N → String) → (L → String) → Tree N L → List String
showSimple nodeStr leafStr = show ([_] ∘′ nodeStr) ([_] ∘′ leafStr)
