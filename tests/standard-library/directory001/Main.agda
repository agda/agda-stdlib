{-# OPTIONS --guardedness #-}

module Main where

open import Data.Bool.Base using (true; false)
open import Data.List.Base as List using (_∷_; [])
open import Data.String.Base using (_++_; unwords)
open import IO
open import Function.Base using (_$_)

open import System.Directory
open import System.FilePath.Posix

main : Main
main = run $ do
  let dirs = "tmp1" ∷ "tmp2" ∷ []
  List.forM′ dirs $ λ d → do
    putStrLn $ "Creating " ++ d
    createDirectory (mkFilePath d)
  ds ← listDirectory (mkFilePath ".")
  List.forM′ ds $ λ d → do
    true ← doesDirectoryExist d
      where false → pure _
    let str = getFilePath d
    putStrLn $ "Saw " ++ str
  List.forM′ dirs $ λ d → do
    putStrLn $ unwords $ "Removing" ∷ d ∷ []
    removeDirectory (mkFilePath d)
