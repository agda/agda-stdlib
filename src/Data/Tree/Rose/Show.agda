------------------------------------------------------------------------
-- The Agda standard library
--
-- 1 dimensional pretty printing of rose trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Rose.Show where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.DifferenceList as DList renaming (DiffList to DList) using ()
open import Data.List.Base as List using (List; []; _∷_; [_])
open import Data.List.NonEmpty.Base as List⁺ using (List⁺; _∷_; _∷⁺_)
open import Data.String.Base using (String; _++_)
open import Data.Tree.Rose using (Rose; node; map)
open import Function.Base using (_∘′_; id; _$_)
open import Level using (Level)

private
  variable
    a : Level
    A : Set a


------------------------------------------------------------------------
-- Main recursive definition

display : Rose (List String) → List String
display t = DList.toList $ goRose [] t DList.[]
  where
  padding : Bool → List Bool → String → String
  padding dir? []       = id
  padding dir? (b ∷ bs) = padding dir? bs ∘′
    ((if dir? ∧ List.null bs
     then if b then " ├ " else " └ "
     else if b then " │ "  else "   ")
    ++_)

  nodePrefix : List Bool → List String → DList String
  nodePrefix bs []       = DList.[]
  nodePrefix bs (s ∷ ss) =
    padding true bs s DList.∷ DList.fromList (List.map (padding false bs) ss)

  childrenPrefixes : List A → List⁺ Bool
  childrenPrefixes []       = false ∷ []
  childrenPrefixes (x ∷ xs) = true ∷⁺ childrenPrefixes xs

  goRose : List Bool → Rose (List String) → DList String → DList String
  goRose bs (node ss ts) dl = nodePrefix bs ss DList.++ go ts DList.++ dl
    where
    goZip : List (List Bool) → List (Rose (List String)) → DList String
    goZip (bs ∷ bss) (t ∷ ts) = goRose bs t $ goZip bss ts
    goZip [] _ = DList.[]
    goZip _ [] = DList.[]

    go : List (Rose (List String)) → DList String
    go []       = DList.[]
    go (t ∷ ts) =
      let bs′ ∷ bss′ = List⁺.map (_∷ bs) (childrenPrefixes ts)
      in goRose bs′ t $ goZip bss′ ts

------------------------------------------------------------------------
-- Corollaries

show : (A → List String) → Rose A → List String
show toString = display ∘′ map toString

showSimple : (A → String) → Rose A → List String
showSimple toString = show ([_] ∘′ toString)
