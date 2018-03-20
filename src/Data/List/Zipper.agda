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


-- Definition
------------------------------------------------------------------------

-- A List Zipper represents a List together with a particular sub-List
-- in focus. The user can attempt to move the focus left or right, with
-- a risk of failure if one has already reached the corresponding end.

-- To make these operations efficient, the `context` the sub List in
-- focus lives in is stored *backwards*. This is made formal by `toList`
-- which returns the List a Zipper represents.

record Zipper {a} (A : Set a) : Set a where
  constructor mkZipper
  field context : List A
        value   : List A

  toList : List A
  toList = List.reverse context List.++ value
open Zipper public

-- Embedding Lists as Zippers without any context
fromList : ∀ {a} {A : Set a} → List A → Zipper A
fromList = mkZipper []

-- Fundamental operations of a Zipper: Moving around
------------------------------------------------------------------------

module _ {a} {A : Set a} where

 left : Zipper A → Maybe (Zipper A)
 left (mkZipper []        val) = nothing
 left (mkZipper (x ∷ ctx) val) = just (mkZipper ctx (x ∷ val))

 right : Zipper A → Maybe (Zipper A)
 right (mkZipper ctx [])        = nothing
 right (mkZipper ctx (x ∷ val)) = just (mkZipper (x ∷ ctx) val)


-- Focus-respecting operations
------------------------------------------------------------------------

module _ {a} {A : Set a} where

 reverse : Zipper A → Zipper A
 reverse (mkZipper ctx val) = mkZipper val ctx

 -- If we think of a List [x₁⋯xₘ] split into a List [xₙ₊₁⋯xₘ] in focus
 -- of another list [x₁⋯xₙ] then there are 4 places (marked {k} here) in
 -- which we can insert new values: [{1}x₁⋯xₙ{2}][{3}xₙ₊₁⋯xₘ{4}]

 -- The following 4 functions implement these 4 insertions.

 -- `xs ˢ++ ys` inserts `xs` on the `s` side of the context of `ys`
 -- `xs ++ˢ ys` insert `ys` on the `s` side of the value in focus of `ys`

 infixr 5 _ˡ++_ _ʳ++_
 infixl 5 _++ˡ_ _++ʳ_
 -- {1}
 _ˡ++_ : List A → Zipper A → Zipper A
 xs ˡ++ mkZipper ctx val = mkZipper (ctx List.++ List.reverse xs) val

 -- {2}
 _ʳ++_ : List A → Zipper A → Zipper A
 xs ʳ++ mkZipper ctx val = mkZipper (List.reverse xs List.++ ctx) val

 -- {3}
 _++ˡ_ : Zipper A → List A → Zipper A
 mkZipper ctx val ++ˡ xs = mkZipper ctx (xs List.++ val)

 -- {4}
 _++ʳ_ : Zipper A → List A → Zipper A
 mkZipper ctx val ++ʳ xs = mkZipper ctx (val List.++ xs)


-- List-like operations
------------------------------------------------------------------------

module _ {a} {A : Set a} where

 length : Zipper A → ℕ
 length (mkZipper ctx val) = List.length ctx + List.length val

module _ {a b} {A : Set a} {B : Set b} where

 map : (A → B) → Zipper A → Zipper B
 map f (mkZipper ctx val) = (mkZipper on List.map f) ctx val

 foldr : (A → B → B) → B → Zipper A → B
 foldr c n (mkZipper ctx val) = List.foldl (flip c) (List.foldr c n val) ctx


-- Generating all the possible foci of a list
------------------------------------------------------------------------

module _ {a} {A : Set a} where

 allFociIn : List A → List A → List (Zipper A)
 allFociIn ctx []           = List.[ mkZipper ctx [] ]
 allFociIn ctx xxs@(x ∷ xs) = mkZipper ctx xxs ∷ allFociIn (x ∷ ctx) xs

 allFoci : List A → List (Zipper A)
 allFoci = allFociIn []
