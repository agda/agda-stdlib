------------------------------------------------------------------------
-- The Agda standard library
--
-- Examples showing how the notion of Interleaving can be used
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README.Data.Interleaving where

open import Level
open import Data.List.Base hiding (filter)
open import Data.List.Relation.Unary.All
open import Function
open import Relation.Nullary
open import Relation.Unary

-- In its most general form, `Interleaving` is parametrised by two relations
-- `L` (for Left) and `R` (for Right). Given three lists, `xs`, `ys` and `zs`,
-- a proof of `Interleaving xs ys zs` is essentially a diagram explaining how
-- `zs` can be pulled apart into `xs` and `ys` in a way compatible with `L`
-- and `R`. For instance:

-- xs               zs               ys
--
-- x₁ -- L x₁ z₁ -- z₁
-- x₂ -- L x₂ z₂ -- z₂
--                  z₃ -- R z₃ z₁ -- y₁
-- x₃ -- L x₃ z₄ -- z₄
--                  z₅ -- R z₅ y₂ -- y₂

open import Data.List.Relation.Ternary.Interleaving.Propositional

-- The special case we will focus on here is the propositional case: both
-- `L` and ̀R` are propositional equality. Rethinking our previous example,
-- this gives us the proof that [z₁, ⋯, z₅] can be partitioned into
-- [z₁, z₂, z₄] on the one hand and [z₃, z₅] in the other.

-- One possible use case for such a relation is the definition of a very
-- precise filter function. Provided a decidable predicate `P`, it will
-- prove not only that the retained values satisfy `P` but that the ones
-- that didn't make the cut satisfy the negation of P.

-- We can make this formal by defining the following record type:

infix 3 _≡_⊎_
record Filter {a p} {A : Set a} (P : Pred A p) (xs : List A) : Set (a ⊔ p) where
  constructor _≡_⊎_
  field
    -- The result of running filter is two lists:
    -- * the elements we have kept
    -- * and the ones we have thrown away
    -- We leave these implicit: they can be inferred from the rest
    {kept}   : List A
    {thrown} : List A
    -- There is a way for us to recover the original
    -- input by interleaving the two lists
    cover    : Interleaving kept thrown xs
    -- Finally, the partition was made according to the predicate
    allP     : All P kept
    all¬P    : All (∁ P) thrown

-- Once we have this type written down, we can write the function.
-- We use an anonymous module to clean up the function's type.

module _ {a p} {A : Set a} {P : Pred A p} (P? : Decidable P) where

  filter : ∀ xs → Filter P xs
  -- If the list is empty, we are done.
  filter []       = [] ≡ [] ⊎ []
  filter (x ∷ xs) =
    -- otherwise we start by running filter on the tail
    let xs' ≡ ps ⊎ ¬ps = filter xs in
    -- And depending on whether `P` holds of the head,
    -- we cons it to the `kept` or `thrown` list.
    case P? x of λ where -- [1]
      (yes p) → consˡ xs' ≡ p ∷ ps ⊎      ¬ps
      (no ¬p) → consʳ xs' ≡     ps ⊎ ¬p ∷ ¬ps



-- [1] See the following module for explanations of `case_of_` and
--     pattern-matching lambdas
import README.Case
