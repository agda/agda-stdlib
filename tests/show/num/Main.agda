{-# OPTIONS --guardedness #-}

module Main where

open import Level
open import Data.List.Base using (List; _∷_; [])
open import Data.String using (unwords)
open import IO
open import Function.Base using (_$_)

import Data.Nat.Base as Nat
import Data.Nat.Show as ShowNat

tests : List Nat.ℕ
tests = 0 ∷ 13 ∷ 42 ∷ 2 Nat.^ 10 ∷ []

nats : IO {0ℓ} _
nats = let open ShowNat in
  List.forM′ tests $ λ n → do
    putStrLn (show n)
    putStrLn (showInBase 2 n)

import Data.Integer.Base as Int
import Data.Integer.Show as ShowInt

ints : IO {0ℓ} _
ints = let open Int; open ShowInt in
  List.forM′ tests $ λ n → do
    putStrLn (show (+ n))
    putStrLn (show (- + n))

import Data.Rational.Unnormalised.Base as URat
import Data.Rational.Unnormalised.Show as ShowURat

urats : IO {0ℓ} _
urats = let open URat; open ShowURat in
  List.forM′ tests $ λ num →
    List.forM′ tests $ λ denum →
      unless (num Nat.≡ᵇ denum) $ do
        putStrLn $ unwords
          $ show (mkℚᵘ (Int.+ num) 0)
          ∷ "*"
          ∷ show (mkℚᵘ (Int.+ 1) denum)
          ∷ "≡"
          ∷ show (mkℚᵘ (Int.+ num) denum)
          ∷ []

import Data.Rational.Base as Rat
import Data.Rational.Show as ShowRat
open import Data.Nat.Coprimality

rats : IO {0ℓ} _
rats = let open Rat; open ShowRat in
  List.forM′ tests $ λ num →
    List.forM′ tests $ λ denum →
      unless (num Nat.≡ᵇ denum) $ do
        putStrLn $ unwords
          $ show (normalize num 1)
          ∷ "*"
          ∷ show (normalize 1 (Nat.suc denum))
          ∷ "≡"
          ∷ show (normalize num (Nat.suc denum))
          ∷ []

main : Main
main = run $ do
  nats
  ints
  urats
  rats
