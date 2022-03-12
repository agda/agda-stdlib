{-# OPTIONS --guardedness --sized-types #-}

module Main where

open import Data.List.Base using (_∷_; [])
open import Data.String.Base using (String; unlines)
open import Data.Tree.Rose
open import Data.Tree.Rose.Show
open import IO.Base
open import IO.Finite
open import Function.Base using (_$_; id)

dependencies : Rose String _
dependencies = node "standard-library"
  $ agda
  ∷ cabal
  ∷ haskell
  ∷ [] where

  haskell : Rose String _
  haskell = node "Haskell"
    $ node "Haskell (bootstrap)" []
    ∷ node "C" []
    ∷ []

  cabal : Rose String _
  cabal = node "cabal" (haskell ∷ [])

  agda : Rose String _
  agda = node "Agda"
    $ haskell
    ∷ cabal
    ∷ node "alex" (haskell ∷ [])
    ∷ node "happy" (haskell ∷ [])
    ∷ []

main : Main
main = run $ do
  putStrLn $ unlines $ showSimple id dependencies
