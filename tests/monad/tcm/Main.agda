{-# OPTIONS --guardedness #-}

module Main where

-- Taken from #1530

open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Unit using (⊤; tt)

open import Reflection.AST.Term
open import Reflection.TCM using (TC; inferType)

open import Effect.Monad
open RawMonad {{...}} public using (pure; _>>=_; _>>_)

open import Data.Maybe.Instances
open import Reflection.TCM.Instances

goalErr : Term → TC ⊤
goalErr goal = do
  goalType ← inferType goal
  pure _
