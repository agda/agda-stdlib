{-# OPTIONS --guardedness #-}

module Main where

open import Data.String.Base
open import Function.Base using (_$_; case_of_)
open import IO
open import System.Exit using (exitSuccess)

main : Main
main = run $ do
  -- Ensure no buffering so that the prompt "echo< "
  -- gets outputed immediately
  hSetBuffering stdout noBuffering
  forever $ do
    putStr "echo< "
    -- Get a line from the user and immediately inspect it
    -- If it's a magic "exit" keyword then we exit, otherwise
    -- we print the echo'd message and let the `forever` action
    -- continue
    str ← getLine
    case str of λ where
      "exit" → exitSuccess
      _ → putStrLn ("echo> " ++ str)
