{-# OPTIONS --guardedness --sized-types #-}

module Main where

open import Data.List.Base as List using (_∷_; [])
open import Data.String.Base as String using (String)
open import Data.Unit.Base using (⊤)
open import Function.Base using (_$_; id)

open import Reflection using (TC; Term; getType; getDefinition)
open import Reflection.AST.Show

macro
  runTC : TC String → Term → TC ⊤
  runTC tc t = let open Reflection in do
    u ← tc
    unify t (lit (string u))

open import IO.Base hiding (_<$>_)
open import IO.Finite

open import Reflection.TCM.Syntax using (_<$>_)

main : Main
main = run $ do
  let name = quote List.map
  putStr   $ showName name String.++ " : "
  putStrLn $ runTC (showTerm <$> getType name)
  putStr   $ showName name String.++ " = "
  putStrLn $ runTC (showDefinition <$> getDefinition name)
