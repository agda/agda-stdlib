{-# OPTIONS --guardedness #-}

module Main where

open import Data.String.Base
open import Function.Base using (_$_)
open import IO
open import System.Exit using (exitSuccess)

main : Main
main = run $ do
  hSetBuffering stdout noBuffering
  forever $ do
    putStr "echo< "
    "exit" ← getLine
      where str → putStrLn ("echo> " ++ str)
    exitSuccess
