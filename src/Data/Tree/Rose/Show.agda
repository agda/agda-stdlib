------------------------------------------------------------------------
-- The Agda standard library
--
-- 1 dimensional pretty printing of rose trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Rose.Show where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.DifferenceList as DList
   using (_++_; fromList; toList)
   renaming (DiffList to DList; [] to []ᴰ; _∷_ to _∷ᴰ_)
open import Data.List.Base as List using (List; []; _∷_; [_])
open import Data.List.NonEmpty.Base as List⁺ using (List⁺; _∷_; _∷⁺_)
open import Data.String.Base as String using (String)
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
display t = toList $ goTree [] t []ᴰ
  where
  padding : Bool → List Bool → String → String
  padding dir? []       = id
  padding dir? (b ∷ bs) =
    ((if dir? ∧ List.null bs
     then if b then " ├ " else " └ "
     else if b then " │ " else "   ")
    String.++_) ∘′ padding dir? bs

  nodePrefix : List Bool → List String → DList String
  nodePrefix bs []       = []ᴰ
  nodePrefix bs (s ∷ ss) = let bsᵒ = List.reverse bs in
    padding true bsᵒ s ∷ᴰ fromList (List.map (padding false bsᵒ) ss)

  childrenPrefixes : List A → List⁺ Bool
  childrenPrefixes []       = false ∷ []
  childrenPrefixes (x ∷ xs) = true ∷⁺ childrenPrefixes xs

  goTree : List Bool → Rose (List String) → DList String → DList String
  goTree bs (node ss ts) dl = nodePrefix bs ss ++ goList ts ++ dl
    where
    goZip : List (List Bool) → List (Rose (List String)) → DList String
    goZip (bs ∷ bss) (t ∷ ts) = goTree bs t $ goZip bss ts
    goZip [] _ = []ᴰ
    goZip _ [] = []ᴰ

    goList : List (Rose (List String)) → DList String
    goList []       = []ᴰ
    goList (t ∷ ts) =
      let bs′ ∷ bss′ = List⁺.map (_∷ bs) (childrenPrefixes ts)
      in goTree bs′ t $ goZip bss′ ts

------------------------------------------------------------------------
-- Corollaries

show : (A → List String) → Rose A → List String
show toString = display ∘′ map toString

showSimple : (A → String) → Rose A → List String
showSimple toString = show ([_] ∘′ toString)
