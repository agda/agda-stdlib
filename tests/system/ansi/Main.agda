{-# OPTIONS --guardedness #-}

module Main where

open import Data.List.Base using ([]; _∷_)
open import IO.Base
open import IO.Finite
open import Function.Base using (_$_)
open import System.Console.ANSI

main : Main
main = run $ do
  putStrLn $ withCommands (setColour foreground classic blue
                          ∷ setColour background classic white
                          ∷ [])
             "Classic blue on white"
  putStrLn $ withCommands (setColour foreground classic white
                          ∷ setColour background bright blue
                          ∷ [])
             "White on bright blue"
  putStrLn $ withCommands (setWeight bold
                          ∷ setColour foreground bright yellow
                          ∷ setColour background bright blue
                          ∷ [])
             "Bold bright yellow on bright blue"
  putStrLn $ withCommands (setStyle italic
                          ∷ setColour foreground bright red
                          ∷ setColour background classic yellow
                          ∷ [])
             "Italic bright red on yellow"
  putStrLn $ withCommands (setBlinking rapid
                          ∷ setUnderline double
                          ∷ setWeight bold
                          ∷ setColour background classic red
                          ∷ setColour foreground bright black
                          ∷ [])
             "PARTYYYY"
