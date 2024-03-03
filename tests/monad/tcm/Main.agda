{-# OPTIONS --guardedness #-}

module Main where

-- Taken from #1530

open import Data.String.Base using (String)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Unit using (⊤; tt)

open import Reflection.AST.Literal
open import Reflection.AST.Term
open import Reflection.AST.Show using (showTerm)
open import Reflection.TCM using (TC; inferType; unify)

open import Effect.Monad
open RawMonad {{...}} public using (pure; _>>=_; _>>_)

open import Data.Maybe.Instances
open import Reflection.TCM.Instances

macro
   goalErr : Term → Term → TC ⊤
   goalErr t goal = do
     goalType ← inferType t
     unify goal (lit (string (showTerm goalType)))


open import IO.Base hiding (_>>=_; _>>_)
open import IO.Finite
open import IO.Instances
open import Function.Base using (_$_)

main : Main
main = run $ do
  putStrLn (goalErr main)
  putStrLn (goalErr putStrLn)
