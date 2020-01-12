------------------------------------------------------------------------
-- The Agda standard library
--
-- 1 dimensional pretty printing of rose trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Text.Tree.Linear where

open import Level using (Level)
open import Size
open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.DifferenceList as DList renaming (DiffList to DList) using ()
open import Data.List.Base as List using (List; []; [_]; _∷_; _∷ʳ_)
open import Data.Nat.Base using (ℕ; _∸_)
open import Data.Product using (_×_; _,_)
open import Data.String.Base
open import Data.Tree.Rose using (Rose; node)
open import Function.Base using (flip)

private
  variable
    a : Level
    A : Set a
    i : Size

display : Rose (List String) i → List String
display t = DList.toList (go (([] , t) ∷ [])) where

  padding : Bool → List Bool → String → String
  padding dir? []       str = str
  padding dir? (b ∷ bs) str =
    (if dir? ∧ List.null bs
     then if b then " ├ " else " └ "
     else if b then " │ "  else "   ")
    ++ padding dir? bs str

  nodePrefixes : List A → List Bool
  nodePrefixes as = true ∷ List.replicate (List.length as ∸ 1) false

  childrenPrefixes : List A → List Bool
  childrenPrefixes as = List.replicate (List.length as ∸ 1) true ∷ʳ false

  go : List (List Bool × Rose (List String) i) → DList String
  go []                       = DList.[]
  go ((bs , node a ts₁) ∷ ts) =
    let bs′ = List.reverse bs in
    DList.fromList (List.zipWith (flip padding bs′) (nodePrefixes a) a)
    DList.++ go (List.zip (List.map (_∷ bs) (childrenPrefixes ts₁)) ts₁)
    DList.++ go ts
