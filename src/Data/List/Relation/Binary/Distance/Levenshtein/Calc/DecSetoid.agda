------------------------------------------------------------------------
-- The Agda standard library
--
-- Levenshtein distance: calculations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (DecSetoid)

module Data.List.Relation.Binary.Distance.Levenshtein.Calc.DecSetoid {c ℓ} (S : DecSetoid c ℓ) where

open import Level using (Level; _⊔_)

open import Data.List.Base
  as List>
  using ([])
  renaming (List to List>; _∷_ to _:>_)

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (∃; _×_; _,_; -,_)

open import Data.SnocList.Base
  as List<
  using (List<; []; _<:_; _<>>_)

open import Data.List.Relation.Unary.Split
  using (Split; _||_; All; Allʳ; []; _:>_; _<:_; stepRight; rightOf; currentˡ; currentʳ)

open import Function.Base using (_$′_)
open import Function.Strict using (_!|>_)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Decidable using (Dec)

module S = DecSetoid S
open S
  renaming (Carrier to A)
  using (_≈_; _≈?_)

open import Data.List.Relation.Binary.Distance.Levenshtein.Dist.Setoid
  S.setoid
  using (Dist; dist-[]ˡ; dist-[]ʳ; module Step)

private
  variable
    x y : A
    xs ys : List> A
    sx sy : List< A

-- We have seen in Data.List.Relation.Binary.Distance.Levenshtein.Dist
-- how we can take a step when computing the Levenshtein distance:
-- if we know the distance between
-- 1. xs and ys
-- 2. xs and (y ∷ ys)
-- 3. (x ∷ xs) and ys
-- then we can compute the distance between (x ∷ xs) and (y ∷ ys)

-- Writing a function repeatedly applying this step to the result of
-- recursive calls is however not practical: each step would induce
-- three separate recursive calls, themselves causing three further
-- recursive calls each, etc.
-- This would lead to an exponential blowup and we would not get our
-- answers without wasting an awful lot of time and computing.

-- Luckily for us, these exponentially-many sub-computations are heavily
-- overlapping. We can see this using a geometric intuition:
-- a split (sx || xs) can be understood as a point somewhere inside the
-- (sx <>> xs) segment (the point at index (length< sx)) and the same is
-- true of the split (sy || ys).
--
-- Correspondly we can draw the rectangle defined by placing (sx <>> xs)
-- and (sy <>> ys) orthogonally. Let us consider the concrete example
-- with 'banana' and 'canada' (sneakily using the unicode character V̈ as
-- a "vertical :>")

--       'b' :> 'a' :> 'n' :> 'a' :> 'n' :> 'a' :> [>]
--  'c'
--   V̈
--  'a'                 X   →  2
--   V̈                  ↓   ↘
--  'n'                 3      1
--   V̈
--  'a'
--   V̈
--  'd'
--   V̈
--   a
--   V̈
--  [>]

-- The position marked `X` corresponds to the splits
--    ([<] :< 'b' :< 'a' || 'n' :> 'a' :> 'n' :> 'a' :> [>])
--    ([<] :< 'c' || 'a' :> 'n' :> 'a' :> 'd' :> 'a' :> [>])
--
-- If we apply `step` to compute the distance at that point, we see that
-- we need to compute the distances at 1 (skipping over both 'n' and 'a'
-- along ↘), 2 (skipping over 'n' in 'banana' along →) and 3 (skipping
-- over 'a' in 'canada' along ↓).

-- Now, if we apply `step` to compute the value in `2` we will need to,
-- among other things, also compute the value at `1` as it's
-- directly below '2' and is reached by skipping over 'a' in 'canada'.
--
-- And applying step to compute the value in `3` requires us to,
-- among other things, also compute the value at `1` at it's
-- directly to the right of `3` and is reached by skipping over 'n'
-- in 'banana'.

-- Indeed moving along ↘ reaches the same destination as moving along
-- either of (→ and then ↓) on the one hand and (↓ and then →) on the
-- other.

-- This is why the Levenshtein distance is typically implemented using
-- *dynamic programming*: instead of constantly recomputing the same
-- distances over and over again, we memoise the intermediate results
-- so as to avoid repeating the work.
-- The rectangle above has a size quadratic in the size of its input
-- and so it will take at most a quadratic amount of time to fill it
-- up. Much better than exponential!


-- Paying a bit more attention to the problem, we notice that we don't
-- even need to carry the whole matrix around! Given a line in the
-- matrix, we can compute the line above it by filling it up right-to-left.
-- We know the rightmost value is given by fromEmpty and we know that
-- we can compute dₙₖ provided we know dₙ₍ₖ₊₁₎, d₍ₙ₊₁₎ₖ, and d₍ₙ₊₁₎₍ₖ₊₁₎.

--  dₙ₁    →    dₙ₂    →  ...   dₙₖ    →  ... fromEmpty
--  ↓      ↘    ↓      ↘  ...   ↓      ↘
-- d₍ₙ₊₁₎₁     d₍ₙ₊₁₎₂    ...  d₍ₙ₊₁₎ₖ    ... d₍ₙ₊₁₎ₘ

-- Correspondingly, at every step of the way we are only interested in
-- the stuff that's to our right and directly below us.

------------------------------------------------------------------------
-- Representing Lines

-- As we said above, to compute a new line, we will assume we have
--    1. the line below us filled in
--    2. everything to our right on the current line already filled in
-- and that should be enough to allow us to slowly fill up the current
-- line.


-- To help the unifier reconstruct the splits in the
-- indices, we unfortunately have to introduce a wrapper
record ADist {xs ys : List> A}
  (spxs : Split xs) (spys : Split ys) : Set (c ⊔ ℓ)
  where
  constructor wrap
  field calc : ∃ (Dist (rightOf spxs) (rightOf spys))
open ADist

step :
  ADist (sx <: x || xs) (sy <: y || ys) →
  ADist (sx <: x || xs) (sy || y :> ys) →
  ADist (sx || x :> xs) (sy <: y || ys) →
  ADist (sx || x :> xs) (sy || y :> ys)
step {x = x} {y = y} dxy dx dy = wrap (Step.step (calc dxy) (calc dx) (calc dy) (x ≈? y))

-- A filled line in the matrix we described earlier is defined by
-- an `All` proof that we have a distance for the suffixes present
-- at every possible split.
Line : {xs ys : List> A} → Split xs → Split ys → Set (Level.suc (c ⊔ ℓ))
Line spl spr = All (λ spl → ADist spl spr) spl

-- As we proceed to fill up the current line, we accumulate values
-- right-to-left up to the current split. Correspondingly, a
-- PartialLine is merely an Allʳ
PartialLine : {xs ys : List> A} → Split xs → Split ys → Set (Level.suc (c ⊔ ℓ))
PartialLine spl spr = Allʳ (λ spl → ADist spl spr) spl

-- Once our partial line has reached the leftmost split
-- (i.e. [<] || xs), we can finalise it into a full line.
finalise : PartialLine ([] || xs) (sy || ys) → Line ([] || xs) (sy || ys)
finalise ([] d)  = [] d
finalise (d :> l) = [] d , l

------------------------------------------------------------------------
-- Computing the Levenshtein distance in a correct by construction manner.

module Line {sy : List< A} {y : A} {ys : List> A} where

  -- By moving right to left slowly build the current line of values
  partialLine :
    ∀ sx (xs : List> A) →
    -- given the full computation of the line below at the current split:
    Line (sx || xs) (sy <: y || ys) →
    -- produce a partial computation of the current line at the current split:
    PartialLine (sx || xs) (sy || y :> ys)
  partialLine sx []        below = [] (wrap (-, dist-[]ˡ))
  partialLine sx (x :> xs) below@(bl , br)
    = partialLine (sx <: x) xs (stepRight below) !|> λ ih →
    step (currentʳ br) (currentʳ ih) (currentˡ bl)
    :> ih

  -- Computing the current line given the line below
  line :
    ∀ (xs : List> A) →
    -- full computation of the line below:
    Line ([] || xs) (sy <: y || ys) →
    -- full computation of the current line:
    PartialLine ([] || xs) (sy || y :> ys)
  line xs below = partialLine [] xs below

-- Computing the bottom line
init : ∀ xs → PartialLine (sx || xs) (sy || [])
init []        = [] (wrap (-, dist-[]ʳ))
init (x :> xs) = (wrap (-, dist-[]ʳ)) :> init xs

compute : (xs ys : List> A) → ∃ (Dist xs ys)
compute xs ys = ADist.calc (currentʳ (go [] ys)) where

  go : ∀ sy (ys : List> A) → PartialLine ([] || xs) (sy || ys)
  go sy []        = init xs
  go sy (y :> ys) = Line.line xs (finalise $′ go (sy <: y) ys)
