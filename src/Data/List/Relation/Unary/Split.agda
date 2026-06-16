------------------------------------------------------------------------
-- The Agda standard library
--
-- List split: identifiying a position inside of a list
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Unary.Split where

open import Data.List.Base
  as List>
  using ([])
  renaming (List to List>; _∷_ to _:>_)

open import Data.Product.Base using (_×_; _,_)

open import Data.SnocList.Base
  as List<
  using (List<; []; _<:_; _<>>_)

open import Level using (Level; _⊔_)

open import Relation.Unary using (Pred)

private
  variable
    a p : Level
    A : Set a
    x : A
    xs : List> A
    sx : List< A
    P : Pred A p

------------------------------------------------------------------------
-- Basic definition

infix 1 _||_
data Split {A : Set a} : Pred (List> A) a where
  _||_ : (sx : List< A) → -- things to the left of the position
         (xs : List> A) → -- things to the right of the position
         Split (sx <>> xs) -- if we put things to the left & to the right side by side,
                           -- we recover the full list

leftOf : Split {A = A} xs → List< A
leftOf (sx || xs) = sx

rightOf : Split {A = A} xs → List> A
rightOf (sx || xs) = xs

private
  variable
    spl : Split xs

------------------------------------------------------------------------
-- Basic functions

moveLeft : Split xs → Split xs
moveLeft (sx <: x || xs) = sx || x :> xs
moveLeft sp = sp

moveRight : Split xs → Split xs
moveRight (sx || x :> xs) = sx <: x || xs
moveRight sp = sp

allSplits : (xs : List> A) → List> (Split xs)
allSplits = go [] module AllSplits where

  go : (sx : List< A) (xs : List> A) → List> (Split (sx <>> xs))
  go sx []        = (sx || [])      :> []
  go sx (x :> xs) = (sx || x :> xs) :> go (sx <: x) xs


------------------------------------------------------------------------
-- Quantifiers over splits

-- All on the left
data Allʳ {p} {A : Set a} : ∀ {xs : List> A} →
  Pred (Split xs) p →
  Pred (Split xs) (a ⊔ Level.suc p)
  where
  -- If we have reached the right end
  []  : ∀ {P}
      → P (sx || [])          -- P holds all the way to the right
      → Allʳ P (sx || [])

  -- If we are considering a split somewhere in the middle
  _:>_ : ∀ {P}
       → P (sx || x :> xs)      -- P holds at the current split
       → Allʳ P (sx <: x || xs) -- P holds everywhere strictly to its right
       → Allʳ P (sx || x :> xs)

currentʳ : Allʳ P spl → P spl
currentʳ ([] d) = d
currentʳ (d :> _) = d

-- All on the right
data Allˡ {p} {A : Set a} : ∀ {xs : List> A} →
  Pred (Split xs) p →
  Pred (Split xs) (a ⊔ Level.suc p)
  where
  -- If we have reached the left end
  []   : ∀ {P}
       → P ([] || xs)           -- P holds all the way to the left
       → Allˡ P ([] || xs)

  -- If we are considering a split somewhere in the middle
  _<:_ : ∀ {P}
       → Allˡ P (sx || x :> xs)  -- P holds everywhere to the left of the current split
       → P (sx <: x || xs)       -- P holds at the current split
       → Allˡ P (sx <: x || xs)

currentˡ : Allˡ P spl → P spl
currentˡ ([] d) = d
currentˡ (_ <: d) = d

-- All, using All on the left & right
All : ∀ {p} {A : Set a} {xs : List> A} →
  Pred (Split xs) p →
  Pred (Split xs) (a ⊔ Level.suc p)
-- If the split is already all the way to the right, then we
-- only need to require that P holds everywhere to its left
All P (sx || [])      = Allˡ P (sx || [])
-- If the split is somewhere in the middle then P should hold
-- everywhere to its left and everywhere *strictly* to its right
All P (sx || x :> xs) = Allˡ P (sx || x :> xs) × Allʳ P (sx <: x || xs)

current : All P spl → P spl
current {spl = _ || []}     ps       = currentˡ ps
current {spl = _ || _ :> _} (ps , _) = currentˡ ps

stepLeft : All P (sx <: x || xs) → All P (sx || x :> xs)
stepLeft {xs = []}     (ls <: d)      = ls , [] d
stepLeft {xs = _ :> _} (ls <: d , rs) = ls , d :> rs

stepRight : All P (sx || x :> xs) → All P (sx <: x || xs)
stepRight {xs = []}     (ls , rs)      = ls <: currentʳ rs
stepRight {xs = _ :> _} (ls , d :> rs) = (ls <: d) , rs
