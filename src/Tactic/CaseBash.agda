------------------------------------------------------------------------
-- The Agda standard library
--
-- The 'case-bash!' tactic automatically case splits on every argument,
-- and then attempting to prove the goal with refl.
-- This allows us to make quick work of some easy proofs.
--
-- ∧-comm : ∀ (x y : Bool) → x ∧ y ≡ y ∧ x
-- ∧-comm = case-bash!
--
-- Limitations:
-- This tactic doesn't handle indexed data well; it is not smart enough
-- to realize that it needs to insert absurd patterns, and will blindly
-- run straight into a type error.
--
-- See README.Tactic.CaseBash for more details
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
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
gatherVisibleDataArgs : Term → TC (List (List Name))
gatherVisibleDataArgs (pi a@(vArg (def nm _)) (abs x b)) = do
  defn ← getDefinition nm
  css ← extendContext x a $ gatherVisibleDataArgs b
  pure $ case defn of λ where
    (data-type _ cs) → layer cs css
    _ → css
gatherVisibleDataArgs (pi a (abs x b)) =
  extendContext x a $ gatherVisibleDataArgs b
gatherVisibleDataArgs _ = pure []

-- Construct a pattern for a constructor type
-- by creating pattern variables for all visible constructor
-- arguments, and add the pattern variables to the current telescope.
--
-- We pass along the length of the telescope to avoid O(n^2)
-- asymptotics from 'length'.
mkConPattern : Term → Telescope → ℕ → Telescope × List (Arg Pattern) × ℕ
mkConPattern (pi (arg i@(arg-info visible m) a) (abs x b)) tele n =
  let (tele , pats , n') = mkConPattern b tele (suc n)
  in (x , arg i (var n [])) ∷ tele , arg i (Pattern.var (pred n')) ∷ pats , n'
mkConPattern (pi (arg _ a) (abs x b)) tele n =
  mkConPattern b tele n
mkConPattern _ tele n = tele , [] , n

-- Construct patterns for a list of constructor names.
-- As before, we need to keep track of the number of pattern variables.
mkConPatterns : List Name → Telescope → ℕ → TC (Telescope × List (Arg Pattern))
mkConPatterns (nm ∷ nms) tele n = do
  con-tp ← getType nm
  let (tele , con-pats , n) = mkConPattern con-tp tele n
  (tele , pats) ← mkConPatterns nms tele n
  pure (tele , (vArg (Pattern.con nm con-pats) ∷ pats))
mkConPatterns [] tele n =
  pure (tele , [])

-- Construct a clause for a list of contructor names.
mkCaseBashClause : List Name → TC Clause
mkCaseBashClause cs = do
  (tele , pats) ← mkConPatterns cs [] 0
  pure $ Clause.clause (reverse tele) pats (con (quote refl) [])

macro
  caseBash! : Term → TC ⊤
  caseBash! hole = do
    goal ← inferType hole
    con-names ← gatherVisibleDataArgs goal
    clauses ← mapA TCM.applicative mkCaseBashClause con-names
    let tm = pat-lam clauses []
    unify hole (pat-lam clauses [])
