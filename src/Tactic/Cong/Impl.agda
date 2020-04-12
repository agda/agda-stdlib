{-# OPTIONS --without-K --safe #-}

module Tactic.Cong.Impl where

open import Category.Monad.State
open import Data.Bool
open import Data.List
open import Data.Nat
open import Data.Product
open import Function.Base
open import Reflection.Abstraction
open import Reflection.Argument
open import Reflection.Name using () renaming (_≟_ to _≟ⁿ_)
open import Reflection.Pattern
open import Reflection.Term
open import Relation.Nullary
open import Tactic.Cong.Common

{- This function turns a term containing ⌞_⌟ into a lambda term with all
   instances of ⌞_⌟ replaced with the argument variable of the lambda.

   Returns the transformed term plus a Bool indicating whether any ⌞_⌟ were
   found. Not finding any ⌞_⌟ generally indicates that the macro has been used
   incorrectly.
-}
extract-f : Term → Term × Bool
extract-f term = let (term , state) = ex 0 term false in (vLam "hole" term , state )
  where
  -- State Monad is used to track whether any ⌞_⌟ have been found
  open Category.Monad.State
  open RawMonadState (StateMonadState Bool)

  ex : ℕ → Term → State Bool Term
  ex-args : ℕ → List (Arg Term) → State Bool (List (Arg Term))
  ex-clauses : ℕ → List Clause → State Bool (List Clause)

  ex hole-i (var var-i args) with does (var-i ≥? hole-i)
  ...                           | true  = do
                                  args ← ex-args hole-i args
                                  return $ var (suc var-i) args
  ...                           | false = do
                                  args ← ex-args hole-i args
                                  return $ var var-i args
  ex hole-i (def f _   )                  with does (f ≟ⁿ quote ⌞_⌟)
  ex hole-i (def _ (_ ⟅∷⟆ _ ⟅∷⟆ _ ⟨∷⟩ args)) | true  = do
                                               put true -- ⌞_⌟ has been found
                                               args ← ex-args hole-i args
                                               return $ var hole-i args
  ex hole-i (def f args)                     | _  = do
                                               args ← ex-args hole-i args
                                               return $ def f args
  ex hole-i (con c args) = do
    args ← ex-args hole-i args
    return $ con c args
  ex hole-i (lam v (abs s t)) = do
    t ← ex (suc hole-i) t
    return $ lam v $ abs s t
  ex hole-i (pat-lam cs args) = do
    cs ← ex-clauses hole-i cs
    args ← ex-args hole-i args
    return $ pat-lam cs args
  ex hole-i (meta x args) = do
    args ← ex-args hole-i args
    return $ meta x args
  ex hole-i (Π[ s ∶ arg v A ] t) = do
    A ← ex hole-i A
    t ← ex (suc hole-i) t
    return $ Π[ s ∶ arg v A ] t
  ex hole-i (sort s) = return $ sort s
  ex hole-i (lit l)  = return $ lit l
  ex hole-i unknown  = return unknown

  ex-args hole-i [] = return []
  ex-args hole-i (arg v t ∷ as) = do
    t ← ex hole-i t
    as ← ex-args hole-i as
    return $ arg v t ∷ as

  ex-clauses hole-i [] = return []
  ex-clauses hole-i (clause ps t ∷ cs) = do
    t ← ex (hole-i + pattern-args-size ps) t
    cs ← ex-clauses hole-i cs
    return $ clause ps t ∷ cs
  ex-clauses hole-i (absurd-clause ps ∷ cs) = do
    cs ← ex-clauses hole-i cs
    return $ absurd-clause ps ∷ cs
