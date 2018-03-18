------------------------------------------------------------------------
-- The Agda standard library
--
-- List Zippers, basic types and operations
------------------------------------------------------------------------

module Data.List.Zipper where

open import Data.Nat.Base
open import Data.Maybe.Base as Maybe using (Maybe ; just ; nothing)
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Function

record Zipper {a} (A : Set a) : Set a where
  constructor mkZipper
  field context : List A
        value   : List A

  toList : List A
  toList = List.reverse context List.++ value
open Zipper public

module _ {a} {A : Set a} where

 length : Zipper A → ℕ
 length (mkZipper ctx val) = List.length ctx + List.length val

 fromList : List A → Zipper A
 fromList = mkZipper []

 reverse : Zipper A → Zipper A
 reverse (mkZipper ctx val) = mkZipper val ctx

 _ˡ++_ : List A → Zipper A → Zipper A
 xs ˡ++ mkZipper ctx val = mkZipper (ctx List.++ List.reverse xs ) val

 _ʳ++_ : List A → Zipper A → Zipper A
 xs ʳ++ mkZipper ctx val = mkZipper (List.reverse xs List.++ ctx) val

 _++ˡ_ : Zipper A → List A → Zipper A
 mkZipper ctx val ++ˡ xs = mkZipper ctx (xs List.++ val)

 _++ʳ_ : Zipper A → List A → Zipper A
 mkZipper ctx val ++ʳ xs = mkZipper ctx (val List.++ xs)

 left : Zipper A → Maybe (Zipper A)
 left (mkZipper []        val) = nothing
 left (mkZipper (x ∷ ctx) val) = just (mkZipper ctx (x ∷ val))

 right : Zipper A → Maybe (Zipper A)
 right (mkZipper ctx [])        = nothing
 right (mkZipper ctx (x ∷ val)) = just (mkZipper (x ∷ ctx) val)

 allFociIn : List A → List A → List (Zipper A)
 allFociIn ctx []           = List.[ mkZipper ctx [] ]
 allFociIn ctx xxs@(x ∷ xs) = mkZipper ctx xxs ∷ allFociIn (x ∷ ctx) xs

 allFoci : List A → List (Zipper A)
 allFoci = allFociIn []

module _ {a b} {A : Set a} {B : Set b} where

 map : (A → B) → Zipper A → Zipper B
 map f (mkZipper ctx val) = (mkZipper on List.map f) ctx val

 foldr : (A → B → B) → B → Zipper A → B
 foldr c n (mkZipper ctx val) = List.foldl (flip c) (List.foldr c n val) ctx
