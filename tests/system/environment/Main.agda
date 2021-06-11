{-# OPTIONS --guardedness #-}

module Main where

open import Data.Maybe.Base using (fromMaybe)
open import Data.String.Base using (unwords)
open import IO
open import Function.Base using (_$_)

open import System.Environment

main : Main
main = run $ do
  prog ← getProgName
  putStrLn prog
  args ← getArgs
  putStrLn $ unwords args
  let var = "AGDA_STDLIB_ENVIRONMENT_TEST"
  setEnv var "hello back!"
  msg ← lookupEnv var
  unsetEnv var
  putStrLn $ fromMaybe ":(" msg
