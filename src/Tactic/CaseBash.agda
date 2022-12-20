------------------------------------------------------------------------
-- The Agda standard library
--
-- When working with non-recursive datatypes, it's common to define
-- functions by exhaustively pattern matching. This is exacerbated
-- by the restrictions that case-trees place on fall-through patterns;
-- such functions do not have good definitional behaviour.
--
-- Writing these functions is tedious, but reasoning about them is
-- even worse. Proofs consist of casing on every single argument, and
-- then proving the goal with 'refl' on the RHS.
--
-- The 'case-bash!' tactic automates this tedium away by case splitting
-- on every argument, and then attempting to prove the goal with refl.
-- This allows us to make quick work of some easy proofs.
--
-- ∧-comm : ∀ (x y : Bool) → x ∧ y ≡ y ∧ x
-- ∧-comm = case-bash!
--
-- Limitations:
-- This tactic doesn't handle indexed data well; it is not smart enough
-- to realize that it needs to insert absurd patterns, and will blindly
-- run straight into a type error.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}
module Tactic.CaseBash where

open import Function.Base
open import Data.Unit.Base
open import Data.List.Base
open import Data.Nat.Base
open import Data.String.Base using (String)
open import Data.Product

open import Data.List.Effectful
import Data.List.Base as List

open import Reflection.AST
open import Reflection.AST.Term
open import Reflection.TCM
open import Reflection.TCM.Syntax
open import Relation.Binary.PropositionalEquality

import Reflection.TCM.Effectful as TCM

open TraversableA

-- Helper function used to construct the clause name lists
layer : ∀ {ℓ} {A : Set ℓ} → List A → List (List A) → List (List A)
layer xs [] = List.map (_∷ []) xs
layer xs yss = cartesianProductWith _∷_ xs yss

-- Gather all of the visible datatype arguments from a pi type,
-- and arrange them into a list of lists of case names.
-- For instance 'Bool → Maybe A → ℕ' would yield the following list:
-- > [[true, just], [true, nothing], [false, just], [false, nothing]]
gather-visible-data-args : Term → TC (List (List Name))
gather-visible-data-args (pi a@(vArg (def nm _)) (abs x b)) = do
  defn ← getDefinition nm
  css ← extendContext a $ gather-visible-data-args b
  pure $ case defn of λ where
    (data-type _ cs) → layer cs css
    _ → css
gather-visible-data-args (pi a (abs x b)) =
  extendContext a $ gather-visible-data-args b
gather-visible-data-args _ = pure []

-- Construct a pattern for a constructor type
-- by creating pattern variables for all visible constructor
-- arguments, and add the pattern variables to the current telescope.
--
-- We pass along the length of the telescope to avoid O(n^2)
-- asymptotics from 'length'.
mk-con-pattern : Term → Telescope → ℕ → Telescope × List (Arg Pattern) × ℕ
mk-con-pattern (pi (arg i@(arg-info visible m) a) (abs x b)) tele n =
  let (tele , pats , n') = mk-con-pattern b tele (suc n)
  in (x , arg i (var n [])) ∷ tele , arg i (Pattern.var (pred n')) ∷ pats , n'
mk-con-pattern (pi (arg _ a) (abs x b)) tele n =
  mk-con-pattern b tele n
mk-con-pattern _ tele n = tele , [] , n

-- Construct patterns for a list of constructor names.
-- As before, we need to keep track of the number of pattern variables.
mk-cons-patterns : List Name → Telescope → ℕ → TC (Telescope × List (Arg Pattern))
mk-cons-patterns (nm ∷ nms) tele n = do
  con-tp ← getType nm
  let (tele , con-pats , n) = mk-con-pattern con-tp tele n
  (tele , pats) ← mk-cons-patterns nms tele n
  pure (tele , (vArg (Pattern.con nm con-pats) ∷ pats))
mk-cons-patterns [] tele n =
  pure (tele , [])

-- Construct a clause for a list of contructor names.
mk-case-bash-clause : List Name → TC Clause
mk-case-bash-clause cs = do
  (tele , pats) ← mk-cons-patterns cs [] 0
  pure $ Clause.clause (reverse tele) pats (con (quote refl) [])

macro
  case-bash! : Term → TC ⊤
  case-bash! hole = do
    goal ← inferType hole
    con-names ← gather-visible-data-args goal
    clauses ← mapA TCM.applicative mk-case-bash-clause con-names
    let tm = pat-lam clauses []
    unify hole (pat-lam clauses [])
