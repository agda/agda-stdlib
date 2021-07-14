{-# OPTIONS --guardedness #-}

module Main where

open import Data.Bool.Base using (true; false)
open import Data.List.Base as List using (_∷_; [])
import Data.List.Sort as Sort
open import Data.String.Base using (_++_; unwords)
import Data.String.Properties as Stringₚ
open import IO
open import Function.Base using (_$_)

open import Relation.Binary
import Relation.Binary.Construct.On as On

open import System.Directory
open import System.FilePath.Posix

decTotalOrder : DecTotalOrder _ _ _
decTotalOrder =
  On.decTotalOrder Stringₚ.≤-decTotalOrder-≈
                   (getFilePath {n = Nature.relative})

open Sort decTotalOrder using (sort)

main : Main
main = run $ do
  let dirs = "tmp1" ∷ "tmp2" ∷ []
  List.forM′ dirs $ λ d → do
    putStrLn $ "Creating " ++ d
    createDirectory (mkFilePath d)
  ds ← listDirectory (mkFilePath ".")
  List.forM′ (sort ds) $ λ d → do
    true ← doesDirectoryExist d
      where false → pure _
    let str = getFilePath d
    putStrLn $ "Saw " ++ str
  List.forM′ dirs $ λ d → do
    putStrLn $ unwords $ "Removing" ∷ d ∷ []
    removeDirectory (mkFilePath d)
