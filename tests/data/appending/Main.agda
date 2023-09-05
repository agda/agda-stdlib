{-# OPTIONS --guardedness #-}

module Main where


open import Data.List.Base using (replicate)
open import Data.String using (toList; fromList)

open import IO
open import Function.Base using (_$_)

open import TakeWhile

main : Main
main = run $ List.sequence′ $ replicate 3 $ do
  str ← getLine
  let taken = takeWhile lower? (toList str)
  putStrLn $ fromList (taken .prefix)
